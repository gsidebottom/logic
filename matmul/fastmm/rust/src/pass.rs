//! Safe multi-threaded drivers for the fused passes: the rows of every block are split into one
//! range per thread; each thread borrows its rows of every output block mutably (disjoint by
//! construction, so the borrow checker proves the absence of data races) and reads the inputs
//! shared.

/// One fused pass of a 4 x 4 scheme with r outputs (the D48 kernels): the 16 blocks of an n x n
/// row-major matrix `a` (leading dimension lda) into r blocks, each m x m with leading dimension
/// m, m = n / 4, over `threads` threads.
pub fn pass_4x4<T, const R: usize>(n: usize, a: &[T], lda: usize, out: &mut [&mut [T]; R], threads: usize,
                                   kernel: fn(usize, [&[T]; 16], [&mut [T]; R]))
where
    T: Copy + Send + Sync,
{
    let m = n / 4;
    let rows = m.div_ceil(threads.max(1));
    std::thread::scope(|s| {
        let mut chunks: Vec<std::slice::ChunksMut<'_, T>> = out.iter_mut().map(|o| o[..m * m].chunks_mut(rows * m)).collect();
        for t in 0..threads {
            let mine: Option<Vec<&mut [T]>> = chunks.iter_mut().map(|it| it.next()).collect();
            let Some(mut mine) = mine else { break };
            let r0 = t * rows;
            s.spawn(move || {
                for (k, r) in (r0..(r0 + rows).min(m)).enumerate() {
                    let i: [&[T]; 16] = std::array::from_fn(|b| {
                        let start = ((b / 4) * m + r) * lda + (b % 4) * m;
                        &a[start..start + m]
                    });
                    let mut it = mine.iter_mut();
                    let o: [&mut [T]; R] = std::array::from_fn(|_| {
                        let ch = it.next().unwrap();
                        &mut ch[k * m..k * m + m]
                    });
                    kernel(m, i, o);
                }
            });
        }
    });
}
