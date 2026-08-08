use std::vec::Vec;

use p3_air::symbolic::SymbolicAirBuilder;
use p3_air::{AirBuilder, ExtensionBuilder, RowWindow};
use p3_field::{Algebra, BasedVectorSpace, ExtensionField, Field, PrimeCharacteristicRing};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrixView;
use p3_matrix::stack::ViewPair;

use p3_uni_stark::{PackedChallenge, PackedVal, StarkGenericConfig, Val};

/// Packed constraint folder for SIMD-optimized prover evaluation.
///
/// Uses packed types to evaluate constraints on multiple domain points simultaneously.
///
/// Collects constraints during `air.eval()` into separate base/ext vectors, then
/// combines them in [`Self::finalize_constraints`] using decomposed alpha powers and
/// `batched_linear_combination` for efficient SIMD accumulation.
#[derive(Debug)]
pub struct ProverConstraintFolder<'a, SC: StarkGenericConfig> {
    /// The [`RowMajorMatrixView`] containing rows on which the constraint polynomial is evaluated.
    pub main: RowMajorMatrixView<'a, PackedVal<SC>>,
    /// The preprocessed columns as a [`RowMajorMatrixView`].
    /// Zero-width when the AIR has no preprocessed trace.
    pub preprocessed: RowMajorMatrixView<'a, PackedVal<SC>>,
    /// Pre-built window over the preprocessed columns.
    pub preprocessed_window: RowWindow<'a, PackedVal<SC>>,
    /// Periodic column values at the current row(s), one packed value per column.
    pub periodic_values: &'a [PackedVal<SC>],
    /// Public inputs to the [AIR](`p3_air::Air`) implementation.
    pub public_values: &'a [Val<SC>],
    /// Evaluations of the first-row selector polynomial.
    /// Non-zero only on the first trace row.
    pub is_first_row: PackedVal<SC>,
    /// Evaluations of the last-row selector polynomial.
    /// Non-zero only on the last trace row.
    pub is_last_row: PackedVal<SC>,
    /// Evaluations of the transition selector polynomial.
    /// Zero only on the last trace row.
    pub is_transition: PackedVal<SC>,
    /// Base-field alpha powers, reordered to match base constraint emission order.
    /// `base_alpha_powers[d][j]` = d-th basis coefficient of alpha power for j-th base constraint.
    pub base_alpha_powers: &'a [Vec<Val<SC>>],
    /// Extension-field alpha powers, reordered to match ext constraint emission order.
    pub ext_alpha_powers: &'a [SC::Challenge],
    /// Collected base-field constraints for this row
    pub base_constraints: Vec<PackedVal<SC>>,
    /// Collected extension-field constraints for this row
    pub ext_constraints: Vec<PackedChallenge<SC>>,
    /// Current constraint index being processed (debug-only bookkeeping)
    pub constraint_index: usize,
    /// Total number of constraints in the AIR (debug-only bookkeeping)
    pub constraint_count: usize,
    /// Stage-2 permutation columns (base-field flattened, D per ext
    /// column; two packed rows: local then next). Zero-width when the
    /// AIR has no stage 2.
    pub perm: RowMajorMatrixView<'a, PackedVal<SC>>,
    /// Stage-2 Fiat-Shamir challenges (sampled after the main commit).
    pub challenges: &'a [SC::Challenge],
}

/// Handles constraint verification for the verifier in a STARK system.
///
/// Similar to [`ProverConstraintFolder`] but operates on committed values rather than the full trace,
/// using a more efficient accumulation method for verification.
#[derive(Debug)]
pub struct VerifierConstraintFolder<'a, SC: StarkGenericConfig> {
    /// Pair of consecutive rows from the committed polynomial evaluations as a [`ViewPair`].
    pub main: ViewPair<'a, SC::Challenge>,
    /// The preprocessed columns as a [`ViewPair`].
    /// Zero-width when the AIR has no preprocessed trace.
    pub preprocessed: ViewPair<'a, SC::Challenge>,
    /// Pre-built window over the preprocessed columns.
    pub preprocessed_window: RowWindow<'a, SC::Challenge>,
    /// Periodic column values at the opened point.
    pub periodic_values: &'a [SC::Challenge],
    /// Public values that are inputs to the computation
    pub public_values: &'a [Val<SC>],
    /// Evaluations of the first-row selector polynomial.
    /// Non-zero only on the first trace row.
    pub is_first_row: SC::Challenge,
    /// Evaluations of the last-row selector polynomial.
    /// Non-zero only on the last trace row.
    pub is_last_row: SC::Challenge,
    /// Evaluations of the transition selector polynomial.
    /// Zero only on the last trace row.
    pub is_transition: SC::Challenge,
    /// Single challenge value used for constraint combination
    pub alpha: SC::Challenge,
    /// Running accumulator for all constraints
    pub accumulator: SC::Challenge,
    /// Stage-2 permutation openings (base-field flattened) at zeta /
    /// zeta_next. Empty when the AIR has no stage 2.
    pub perm_local: &'a [SC::Challenge],
    pub perm_next: &'a [SC::Challenge],
    /// Stage-2 Fiat-Shamir challenges.
    pub challenges: &'a [SC::Challenge],
}

impl<SC: StarkGenericConfig> ProverConstraintFolder<'_, SC> {
    /// Combine all collected constraints with their pre-computed alpha powers.
    ///
    /// Base constraints use [`Algebra::batched_linear_combination`] per basis dimension,
    /// decomposing the extension-field multiply into D base-field SIMD dot products.
    /// Extension constraints use the same method with scalar EF coefficients.
    ///
    /// We keep base and extension constraints separate because the base constraints can
    /// stay in the base field and use packed SIMD arithmetic. Decomposing EF powers of
    /// `alpha` into base-field coordinates turns the base-field fold into a small number
    /// of packed dot-products, avoiding repeated cross-field promotions.
    #[inline]
    pub fn finalize_constraints(&self) -> PackedChallenge<SC> {
        debug_assert_eq!(self.constraint_index, self.constraint_count);

        let base = &self.base_constraints;
        let base_powers = self.base_alpha_powers;
        let acc = PackedChallenge::<SC>::from_basis_coefficients_fn(|d| {
            PackedVal::<SC>::batched_linear_combination(base, &base_powers[d])
        });
        acc + PackedChallenge::<SC>::batched_linear_combination(
            &self.ext_constraints,
            self.ext_alpha_powers,
        )
    }
}

impl<'a, SC: StarkGenericConfig> AirBuilder for ProverConstraintFolder<'a, SC> {
    type F = Val<SC>;
    type Expr = PackedVal<SC>;
    type Var = PackedVal<SC>;
    type PreprocessedWindow = RowWindow<'a, PackedVal<SC>>;
    type MainWindow = RowWindow<'a, PackedVal<SC>>;
    type PublicVar = Val<SC>;
    type PeriodicVar = PackedVal<SC>;

    #[inline]
    fn main(&self) -> Self::MainWindow {
        RowWindow::from_view(&self.main)
    }

    fn preprocessed(&self) -> &Self::PreprocessedWindow {
        &self.preprocessed_window
    }

    #[inline]
    fn is_first_row(&self) -> Self::Expr {
        self.is_first_row
    }

    #[inline]
    fn is_last_row(&self) -> Self::Expr {
        self.is_last_row
    }

    #[inline]
    fn is_transition(&self) -> Self::Expr {
        self.is_transition
    }

    #[inline]
    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        self.base_constraints.push(x.into());
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zeros<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]) {
        let expr_array = array.map(Into::into);
        self.base_constraints.extend(expr_array);
        self.constraint_index += N;
    }

    #[inline]
    fn public_values(&self) -> &[Self::PublicVar] {
        self.public_values
    }

    #[inline]
    fn periodic_values(&self) -> &[Self::PeriodicVar] {
        self.periodic_values
    }
}

impl<SC: StarkGenericConfig> ExtensionBuilder for ProverConstraintFolder<'_, SC> {
    type EF = SC::Challenge;
    type ExprEF = PackedChallenge<SC>;
    type VarEF = PackedChallenge<SC>;

    fn assert_zero_ext<I>(&mut self, x: I)
    where
        I: Into<Self::ExprEF>,
    {
        self.ext_constraints.push(x.into());
        self.constraint_index += 1;
    }
}

impl<'a, SC: StarkGenericConfig> AirBuilder for VerifierConstraintFolder<'a, SC> {
    type F = Val<SC>;
    type Expr = SC::Challenge;
    type Var = SC::Challenge;
    type PreprocessedWindow = RowWindow<'a, SC::Challenge>;
    type MainWindow = RowWindow<'a, SC::Challenge>;
    type PublicVar = Val<SC>;
    type PeriodicVar = SC::Challenge;

    fn main(&self) -> Self::MainWindow {
        RowWindow::from_two_rows(self.main.top.values, self.main.bottom.values)
    }

    fn preprocessed(&self) -> &Self::PreprocessedWindow {
        &self.preprocessed_window
    }

    fn is_first_row(&self) -> Self::Expr {
        self.is_first_row
    }

    fn is_last_row(&self) -> Self::Expr {
        self.is_last_row
    }

    fn is_transition(&self) -> Self::Expr {
        self.is_transition
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        self.accumulator *= self.alpha;
        self.accumulator += x.into();
    }

    fn public_values(&self) -> &[Self::PublicVar] {
        self.public_values
    }

    #[inline]
    fn periodic_values(&self) -> &[Self::PeriodicVar] {
        self.periodic_values
    }
}

/// Stage-2 access for two-stage AIRs: permutation columns committed
/// AFTER the main trace, with challenges sampled in between. Columns
/// are stored base-field-flattened (D base columns per extension
/// column); this trait reconstructs extension values per folder.
pub trait TwoStageBuilder: ExtensionBuilder {
    /// Number of extension-field permutation columns.
    fn perm_ext_width(&self) -> usize;
    /// Extension value of perm column `i` on the current row.
    fn perm_local_ext(&self, i: usize) -> Self::ExprEF;
    /// Extension value of perm column `i` on the next row.
    fn perm_next_ext(&self, i: usize) -> Self::ExprEF;
    /// Stage-2 challenge `i`.
    fn ts_challenge(&self, i: usize) -> Self::ExprEF;
}

impl<SC: StarkGenericConfig> TwoStageBuilder for ProverConstraintFolder<'_, SC> {
    fn perm_ext_width(&self) -> usize {
        let d = <SC::Challenge as BasedVectorSpace<Val<SC>>>::DIMENSION;
        self.perm.width() / d
    }
    fn perm_local_ext(&self, i: usize) -> Self::ExprEF {
        let d = <SC::Challenge as BasedVectorSpace<Val<SC>>>::DIMENSION;
        PackedChallenge::<SC>::from_basis_coefficients_fn(|k| self.perm.get(0, i * d + k).unwrap())
    }
    fn perm_next_ext(&self, i: usize) -> Self::ExprEF {
        let d = <SC::Challenge as BasedVectorSpace<Val<SC>>>::DIMENSION;
        PackedChallenge::<SC>::from_basis_coefficients_fn(|k| self.perm.get(1, i * d + k).unwrap())
    }
    fn ts_challenge(&self, i: usize) -> Self::ExprEF {
        let ch = self.challenges[i];
        PackedChallenge::<SC>::from_basis_coefficients_fn(|k| {
            PackedVal::<SC>::from(
                <SC::Challenge as BasedVectorSpace<Val<SC>>>::as_basis_coefficients_slice(&ch)[k],
            )
        })
    }
}

impl<SC: StarkGenericConfig> ExtensionBuilder for VerifierConstraintFolder<'_, SC> {
    type EF = SC::Challenge;
    type ExprEF = SC::Challenge;
    type VarEF = SC::Challenge;

    fn assert_zero_ext<I>(&mut self, x: I)
    where
        I: Into<Self::ExprEF>,
    {
        self.accumulator *= self.alpha;
        self.accumulator += x.into();
    }
}

impl<SC: StarkGenericConfig> TwoStageBuilder for VerifierConstraintFolder<'_, SC> {
    fn perm_ext_width(&self) -> usize {
        let d = <SC::Challenge as BasedVectorSpace<Val<SC>>>::DIMENSION;
        self.perm_local.len() / d
    }
    fn perm_local_ext(&self, i: usize) -> Self::ExprEF {
        let d = <SC::Challenge as BasedVectorSpace<Val<SC>>>::DIMENSION;
        (0..d)
            .map(|k| {
                self.perm_local[i * d + k]
                    * SC::Challenge::ith_basis_element(k).unwrap()
            })
            .sum()
    }
    fn perm_next_ext(&self, i: usize) -> Self::ExprEF {
        let d = <SC::Challenge as BasedVectorSpace<Val<SC>>>::DIMENSION;
        (0..d)
            .map(|k| {
                self.perm_next[i * d + k]
                    * SC::Challenge::ith_basis_element(k).unwrap()
            })
            .sum()
    }
    fn ts_challenge(&self, i: usize) -> Self::ExprEF {
        self.challenges[i]
    }
}

/// Symbolic stand-in: the SAME eval() call sequence must be emitted as
/// on the real folders (alpha-power tables align by emission order),
/// with faithful DEGREES: perm values are degree-1 (a main-trace
/// symbolic variable stands in), challenges are degree-0 constants.
impl<F: Field, EF: ExtensionField<F>> TwoStageBuilder for SymbolicAirBuilder<F, EF>
where
    p3_air::symbolic::SymbolicExpressionExt<F, EF>: Algebra<EF>,
{
    fn perm_ext_width(&self) -> usize {
        usize::MAX // callers must not size loops from the symbolic pass
    }
    fn perm_local_ext(&self, _i: usize) -> Self::ExprEF {
        let v: Self::Expr = self.main().get(0, 0).unwrap().into();
        Self::ExprEF::ZERO + v
    }
    fn perm_next_ext(&self, _i: usize) -> Self::ExprEF {
        let v: Self::Expr = self.main().get(0, 0).unwrap().into();
        Self::ExprEF::ZERO + v
    }
    fn ts_challenge(&self, _i: usize) -> Self::ExprEF {
        Self::ExprEF::ONE
    }
}

/// Proof produced by the two-stage prover: the standard proof parts
/// plus the stage-2 commitment and its openings.
pub struct TsProof<SC: StarkGenericConfig> {
    pub proof: p3_uni_stark::Proof<SC>,
    pub perm_commit:
        Option<<SC::Pcs as p3_commit::Pcs<SC::Challenge, SC::Challenger>>::Commitment>,
    pub perm_local: Vec<SC::Challenge>,
    pub perm_next: Vec<SC::Challenge>,
    pub perm_width: usize,
    pub num_challenges: usize,
}
