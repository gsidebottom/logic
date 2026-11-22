#!/usr/bin/env python3
"""products_readme.py STAGE README_IN: STAGE/README.md = README_IN (mat_mul's README) with the product and
deletion results of STAGE/products/index.json: the index subsection between <!-- products:begin --> and
<!-- products:end -->, the subsection under "The schemes", and the small edits to the opening, the status
paragraph, Files, Checking and Credits.  Every count in the text is computed here from the index and the plans.
Reads README_IN, writes only STAGE/README.md."""
import json, os, sys
stage, readme_in = sys.argv[1], sys.argv[2]
P = os.path.join(stage, 'products')
rows = json.load(open(os.path.join(P, 'index.json')))
pr = [r for r in rows if r['kind'] == 'product']; de = [r for r in rows if r['kind'] == 'deletion']


def blocks(v, acc):
    """The replaced blocks of a plan: 'subspace' (explicit vectors), 'grid' (two dimensions above 1), 'single'."""
    if isinstance(v, dict):
        if v.get('op') == 'shared':
            for g in v['groups']:
                acc.add('subspace' if 'vectors' in g else 'grid' if 'cells' in g and sum(t > 1 for t in g['type']) >= 2 else 'single')
        for x in v.values(): blocks(x, acc)
    elif isinstance(v, list):
        for x in v: blocks(x, acc)
    return acc


n40 = nsub = ngrid = 0
for r in pr:
    t = open(os.path.join(P, r['folder'], 'plan.json')).read()
    k = blocks(json.loads(t), set())
    n40 += '3x3x6_m40_DPS-accurate.json' in t; nsub += 'subspace' in k; ngrid += 'grid' in k


def fmt(n): return '⟨%d×%d×%d⟩' % tuple(n)
def link(r): return '[%s](products/%s)' % (fmt(r['shape']), r['folder'])
def inv(r): return ', '.join(map(str, r['primes'])) or 'none'
def rings(rs): return tuple(sum(r['ring'] == k for r in rs) for k in ('integer', 'dyadic', 'rational'))
def base(r): return '⟨%d×%d×%d:%d⟩ | %s' % (*r['base_shape'], r['base_rank'], fmt(r['block_sizes']))      # two table cells
def dels(r): return ', '.join('`%s`' % x for x in r['deletions'].split(','))


def source(r): return '⟨%d×%d×%d:%d⟩' % (*r['source'], r['source_rank'])


best = min(rows, key=lambda r: r['omega'])
r336 = sorted((r for r in de if r['source'] == [9, 18, 18] and r['source_rank'] == 1600), key=lambda r: -r['rank'])
assert len(r336) == 5 and all(r['own'] > 0 for r in rows)
A = []
A.append('#### Larger formats: shared-factor products, and deletions from them\n')
A.append('%d formats with a dimension above 16, each below Sedoglavic\'s table of 2026-11-15 and none implied by that table\n'
         'together with the other schemes of this repository (by taking a sub-format, splitting a dimension or a Kronecker\n'
         'product).  The full table is [products/INDEX.md](products/INDEX.md); the largest gains are below.\n' % len(rows))
A.append('- **Products (%d formats, below the table by %d to %d products, %s in total).**  Each is a Kronecker product of\n'
         '  a base scheme with a second format, the block sizes, in which every group of base products that share a factor\n'
         '  is replaced by one scheme of a larger format (a worked example is in\n'
         '  [the method section](#the-schemes-of-products-shared-factor-products)).  This is the serendipitous product as Perminov defines and uses it in\n'
         '  [arXiv:2606.02480](https://arxiv.org/abs/2606.02480) (Section 2.5), where he attributes it to Smith and its\n'
         '  general form to Sedoglavic; the base schemes come from Perminov\'s catalog.  The method and the base schemes are\n'
         '  theirs.  Ours is a screen in which every rank is the rank of a scheme we hold or can build, a builder that\n'
         '  carries out each plan, and the exact check of the result.' % (
             len(pr), min(r['gain'] for r in pr), max(r['gain'] for r in pr), format(sum(r['gain'] for r in pr), ',')))
A.append('- **Deletions (%d formats, below the table by %d to %d, %s in total).**  One index deleted from a product scheme\n'
         '  (two for three of them), followed by LITA\'s 2-reduction, as for the schemes of `large/`.  Part of each gain is\n'
         '  inherited from the product scheme; "Own" in the table is what the deletion adds beyond what the table and our\n'
         '  other schemes imply (%d to %d).' % (
             len(de), min(r['gain'] for r in de), max(r['gain'] for r in de), format(sum(r['gain'] for r in de), ','),
             min(r['own'] for r in de), max(r['own'] for r in de)))
assert sum(',' in r['deletions'] for r in de) == 3
A.append('- **Coefficients.**  Products: %d integer, %d over ℤ[1/2], %d with other denominators.  Deletions: %d integer,\n'
         '  %d over ℤ[1/2], %d with other denominators.  "Invertible" lists the primes that occur in denominators.' % (*rings(pr), *rings(de)))
A.append('- **Form.**  Compressed JSON in [products/](products), one folder per scheme with its build plan or deletion path\n'
         '  and its certificate: see [Files](#files).  Each was certified by evaluating every Brent equation in exact integer\n'
         '  arithmetic ([checks/check_products.log](checks/check_products.log)).')
A.append('- **Exponents.**  None is near a record: the lowest is %.4f (%s:%d), against 2.7743 for ⟨3×3×6:40⟩.\n' % (
    best['omega'], fmt(best['shape']), best['rank']))
A.append('Largest relative gains among the products.  "Base scheme" is the catalog scheme the product starts from.  "Block\n'
         'sizes" ⟨p×q×s⟩ is the second format: every entry of A becomes a p×q block, every entry of B a q×s block and every\n'
         'entry of C a p×s block.  Position by position the two multiply to the format: ⟨11×4×3⟩ with blocks ⟨1×3×6⟩ is\n'
         '⟨11×12×18⟩.  Every scheme is stored with its dimensions in that order; the catalog file may hold the base scheme\n'
         'with its dimensions in another order (here ⟨3×4×11⟩), and the plan says how it is turned.\n')
A.append('| Format | Rank | Table | Gain | Base scheme | Block sizes | Invertible | Exponent (table\'s) |\n|---|---|---|---|---|---|---|---|')
for r in sorted(pr, key=lambda r: -r['gain'] / r['table'])[:15]:
    assert [x * y for x, y in zip(r['base_shape'], r['block_sizes'])] == r['shape']
    A.append('| %s | %d | %d | %d (%.1f%%) | %s | %s | %.4f (%.4f) |' % (
        link(r), r['rank'], r['table'], r['gain'], 100 * r['gain'] / r['table'], base(r), inv(r), r['omega'], r['omega_table']))
A.append('\nLargest own gains among the deletions, relative to the table\'s rank.  "From" is the product scheme and the\n'
         'deleted index, named as for `large/`: in ⟨m×k×n⟩, `I17` removes row 17 of A (and of C), `J17` the inner index 17 (a\n'
         'column of A with the matching row of B) and `K17` column 17 of B, counted from 0.  So ⟨12×13×18:1662⟩, `K17` is\n'
         'that scheme without the last column of B, a scheme for ⟨12×13×17⟩.  The source is written in the orientation in\n'
         'which the deletion leaves the dimensions sorted, so it can be a product scheme of the list turned: ⟨12×11×18:1400⟩\n'
         'is the ⟨11×12×18⟩ scheme of the table above.\n')
A.append('| Format | Rank | Table | Gain | Own | From | Invertible | Exponent (table\'s) |\n|---|---|---|---|---|---|---|---|')
for r in sorted(de, key=lambda r: -r['own'] / r['table'])[:10]:
    assert [a - sum(x[0] == 'IJK'[i] for x in r['deletions'].split(',')) for i, a in enumerate(r['source'])] == r['shape']
    A.append('| %s | %d | %d | %d | %d | %s, %s | %s | %.4f (%.4f) |' % (
        link(r), r['rank'], r['table'], r['gain'], r['own'], source(r), dels(r), inv(r), r['omega'], r['omega_table']))
A.append('\nFive of the deletions start from the plain Kronecker product of ⟨3×3×6:40⟩ with ⟨3×6×3:40⟩, a scheme for\n'
         '⟨9×18×18⟩ of rank 40 · 40 = 1600, which ties the table: %s.' % (
    ', '.join('%s %d (table %d)' % (fmt(r['shape']), r['rank'], r['table']) for r in r336)))
block = '<!-- products:begin -->\n' + '\n'.join(A) + '\n<!-- products:end -->\n'

w = next(r for r in pr if r['shape'] == [11, 12, 18])
assert w['rank'] == 1400 and w['table'] == 1476 and w['base_shape'] == [11, 4, 3] and w['base_rank'] == 104 and w['block_sizes'] == [1, 3, 6]
# as the plan builds it, before it is turned: base <3x4x11>, blocks <6x3x1>, groups of 4, 3 and 2 replaced by <6x3x4>, <6x3x3>, <6x3x2>
assert w['built']['base'] == [3, 4, 11] and w['built']['block_sizes'] == [6, 3, 1]
assert sorted(map(json.dumps, w['built']['replaced'])) == sorted(map(json.dumps, 15 * [[[1, 1, 4], [6, 3, 4]]] + 14 * [[[1, 1, 3], [6, 3, 3]]] + [[[1, 1, 2], [6, 3, 2]]]))
x17 = next(r for r in de if r['shape'] == [12, 13, 17])
assert source(x17) == '⟨12×13×18:1662⟩' and x17['deletions'] == 'K17'
ex = next(r for r in pr if r['shape'] == [9, 9, 27]); exd = next(r for r in de if r['shape'] == [9, 17, 17])
C = '''### The schemes of products/: shared-factor products

**The product.**  Take a base scheme for ⟨a×b×c⟩ with r products and a second format ⟨p×q×s⟩, the block sizes: every
entry of A becomes a p×q block, every entry of B a q×s block, every entry of C a p×s block, and the result is a scheme
for ⟨ap×bq×cs⟩.  The plain Kronecker product replaces each base product by a scheme of ⟨p×q×s⟩ and has rank
r · R(p,q,s).  If g of the base products have the same factor on B up to a scalar, then after blocking that factor
is one q×s block matrix Y and the g other factors are p×q blocks X₁, …, X_g, and the g block products X₁·Y, …, X_g·Y
are one product: the X's stacked into a gp×q matrix, times Y.  So the group can be replaced by one scheme of
⟨gp×q×s⟩, at R(gp,q,s) instead of g · R(p,q,s).  A shared factor on A gives ⟨p×q×gs⟩ in the same way (the other
factors side by side), and one on C gives ⟨p×gq×s⟩.  That is the serendipitous product of Section 2.5 of Perminov's
paper, which attributes it to Smith and its general form to Sedoglavic (a scheme written as a sum of blocks, each
block replaced by a scheme of the block's format times the second format).  The paper applies it across the catalog;
the groups of base products sharing a factor are its "buds", a term it credits to Sedoglavic.

Example 1: ⟨11×4×3:104⟩ with block sizes ⟨1×3×6⟩ gives ⟨11×12×18⟩.  The plain Kronecker product turns each of the 104
base products into a row vector times a 3×6 matrix, 18 multiplications: 104 · 18 = 1872.  The 104 base products fall
into 30 groups that share their factor on B:

| Groups | Products in each | Replaced by | Cost |
|---|---|---|---|
| 15 | 4 | ⟨4×3×6:54⟩ | 810 |
| 14 | 3 | ⟨3×3×6:40⟩ | 560 |
| 1 | 2 | ⟨2×3×6:30⟩ | 30 |

That is 1400 for ⟨11×12×18⟩, where the table has 1476.

Example 2: the catalog's ⟨3×3×9:63⟩ has 27 pairs of products that share a factor.  With block sizes ⟨3×3×3⟩,
each pair is replaced by a scheme of ⟨3×3×6⟩ of rank 40 and each of the other 9 products by ⟨3×3×3:23⟩:
27 · 40 + 9 · 23 = 1287 for ⟨9×9×27⟩, where the table has 1343 and the plain product has 63 · 23 = 1449.

**What we did.**  Perminov's paper reports ranks; many of them need a scheme for every format that appears in a
replacement, and those in turn may be sub-formats, direct sums or products of other schemes.

1. *A screen that only uses what can be built.*  Every rank in a plan is the rank of a scheme we hold as a file, or
   of one that sub-format, direct sum or Kronecker product gives from such files.  The bar a plan has to beat is
   Sedoglavic's table closed under the same three operations.
2. *A builder.*  `kronexact build` executes a plan down to its files and writes the scheme.
3. *An exact check* of every result, as for `large/`, and a second check by other code (random matrices modulo four
   primes).

864 schemes were built this way; %(npr)d are listed.  %(n40)d of the listed ones use the rank-40 scheme of ⟨3×3×6⟩ as a
replacing block, which the catalog's JSON files do not have (they have rank 42).  It is Smirnov's scheme in the
accurate form of Dumas, Pernet and Sedoglavic, PLinOpt's `data/3x3x6_40_DPS-accurate`, here as
[products/base/3x3x6_m40_DPS-accurate.json](products/base/3x3x6_m40_DPS-accurate.json).

**Blocks with two dimensions.**  Products that share factors in two slots form a grid, an image of ⟨1×q×r⟩ (Section
2.6.4 of Perminov's paper).  %(ngrid)d of the listed schemes use one.  %(nsub)d use a variant in which the factors of four
products lie in a plane in each of two slots without being proportional; their sum is still an image of ⟨1×2×2⟩.
Where we built the same format with and without them, either gained 1 to 12 products.

**Deletions.**  The product schemes do not 2-reduce as they stand (we tried the 40 of lowest rank).  After deleting
one index they do.  We searched every product scheme of rank up to 4000, deleting the first and the last index of
each slot: 628 results below the table, all certified, of which the best per format that is not implied by other
schemes is listed (%(nde)d, with the five from ⟨9×18×18:1600⟩ below).  Product schemes above rank 4000 were not searched.

**Exponent.**  We also tried ⟨3×3×6:40⟩ for a better exponent.  No rank-40 scheme we hold has two products sharing a
factor, the ⟨9×18×18:1600⟩ products do not 2-reduce, and every deletion moves the exponent away from 2.7743.  The
five deletions listed above are what that attempt left.

**To reproduce.**  The plans name the catalog's files by their paths in
[Perminov's catalog](https://github.com/dronperminov/FastMatrixMultiplication) at commit f70078c, so a checkout of
that commit is needed; the other files they name are in this repository.  Every scheme file is, byte for byte, the
compressed output of one command run in its folder, and `certificate.log` is what that command printed:

```sh
cargo build --release --manifest-path tools/kronexact/Cargo.toml
KX=$PWD/tools/kronexact/target/release/kronexact
cd products/%(ex)s                  # a product
$KX build plan.json out.json --catalog /path/to/FastMatrixMultiplication
gunzip -c %(exf)s | cmp - out.json
cd ../%(exd)s                # a deletion: builds the product scheme, then replays the path
$KX replay source_plan.json path_1.json out.json --catalog /path/to/FastMatrixMultiplication
gunzip -c %(exdf)s | cmp - out.json
```

Both commands end with the exact check of what they wrote.

''' % dict(npr=len(pr), nde=len(de), n40=n40, ngrid=ngrid, nsub=nsub, ex=ex['folder'], exf=ex['scheme'], exd=exd['folder'], exdf=exd['scheme'])

s = open(readme_in).read()


def rep(a, b):
    global s
    assert s.count(a) == 1, (s.count(a), a[:80])
    s = s.replace(a, b)


rep('The rank records\nfor formats with a dimension above 16 are in `large/`, as compressed JSON with an exact certificate each.',
    'The rank records\nfor formats with a dimension above 16 are in `large/` (deletions from LITA\'s squares) and `products/` (shared-factor\n'
    'products and deletions from them), as compressed JSON with an exact certificate each.')
rep('and the schemes of `large/` are\ncompared with it (commit 8e6ad05).', 'and the schemes of `large/` and\n`products/` are compared with it (commit 8e6ad05).')
if '<!-- products:begin -->' in s:
    i, j = s.index('<!-- products:begin -->'), s.index('<!-- products:end -->\n') + len('<!-- products:end -->\n')
    s = s[:i] + block + s[j:]
else:
    rep('<!-- large:end -->\n', '<!-- large:end -->\n\n' + block)
rep('these schemes would be tens of megabytes each, so they are not included.\n',
    'these schemes would be tens of megabytes each, so they are not included.\n\n'
    '`products/` has one folder per scheme, named like those of `large/`:\n\n'
    '- `SHAPE_mRANK.json.gz`: the scheme, in the same layout as in `large/`, with its dimensions in the order of the\n'
    '  folder name.\n'
    '- For a product, `plan.json`: the base scheme, the block sizes (the second format) and, for every group of base\n'
    '  products that share a factor, the products in it and the scheme that replaces it, each given down to files.  A file node names a file of Perminov\'s\n'
    '  catalog at commit f70078c by its path there (`"catalog"`) or a file of this repository by its path from the\n'
    '  plan\'s folder (`"here"`); a `trivial` node is the schoolbook scheme of a format.  The plan forms the product with\n'
    '  the base scheme as its file has it and ends with the rotations and transpositions that sort the dimensions.\n'
    '  `tools/kronexact build plan.json OUT --catalog DIR` carries it out.\n'
    '- For a deletion, `source_plan.json` (the plan of the product scheme it starts from) and `path_1.json` (the\n'
    '  deletions and their reductions, as in `large/`).  `tools/kronexact replay source_plan.json path_1.json OUT\n'
    '  --catalog DIR` builds the product scheme and redoes the path.\n'
    '- `certificate.log`: the output of that build or replay, which ends with the exact check.\n\n'
    '`products/base/` holds the one base scheme that is in neither place.\n'
    '[products/index.json](products/index.json) and [products/INDEX.md](products/INDEX.md) are the full table.\n')
rep('EXACT=1 tools/check_large.sh                    # large/: also every Brent equation, in exact integers\n',
    'EXACT=1 tools/check_large.sh                    # large/: also every Brent equation, in exact integers\n'
    'tools/check_large.sh products                   # products/: random matrices modulo four primes\n'
    'EXACT=1 tools/check_large.sh products           # products/: also every Brent equation, in exact integers\n')
rep('''  MerlijnW70's schemes and the nine schemes that nine of the records of 2026-11-20 start from, and his 58-addition
  scheme cn122, the start of the 55.
- Alexandre Sedoglavic's table at [fmm.univ-lille.fr](https://fmm.univ-lille.fr/) and
  [sedoglavic/fmm_digest](https://github.com/sedoglavic/fmm_digest).
''', '''  MerlijnW70's schemes and the nine schemes that nine of the records of 2026-11-20 start from; the base schemes
  of all but five of the schemes of `products/`; his paper [arXiv:2606.02480](https://arxiv.org/abs/2606.02480), whose
  shared-factor product those schemes are built with; and his 58-addition scheme cn122, the start of the 55.
- Alexandre Sedoglavic's table at [fmm.univ-lille.fr](https://fmm.univ-lille.fr/) and
  [sedoglavic/fmm_digest](https://github.com/sedoglavic/fmm_digest), and the general form of the serendipitous
  product, which Perminov's paper attributes to him.
- Warren D. Smith, to whose report *Fast matrix multiplication formulae* (technical report, 2002) Perminov's
  paper attributes the serendipitous product.  We have not found a copy of the report and rely on that paper's
  account of it.
- Smirnov's ⟨3×3×6:40⟩, in Dumas, Pernet and Sedoglavic's accurate form (PLinOpt's `data/3x3x6_40_DPS-accurate`),
  the replacing block in %d of the listed product schemes.
''' % n40)
rep('### The rectangular schemes: projection and 2-reduction\n', C + '### The rectangular schemes: projection and 2-reduction\n')
assert '/Users' not in s
open(os.path.join(stage, 'README.md'), 'w').write(s)
print('README.md written: %d products, %d deletions; rank-40 block in %d, grids %d, subspace variant %d; rings %s / %s; lowest exponent %.4f' % (
    len(pr), len(de), n40, ngrid, nsub, rings(pr), rings(de), best['omega']))
