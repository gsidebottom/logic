// BabyBear radix-2 NTT stage kernels (Montgomery domain), matching
// benchntt_bb's CPU semantics exactly: bit-reverse permute, then DIT
// butterfly stages len = 2,4,...,n with per-stage twiddle tables.
#include <metal_stdlib>
using namespace metal;

constant uint P  = 0x78000001u;
constant uint NP = 0x77ffffffu;

inline uint mont_mul(uint a, uint b) {
    uint lo = a * b;
    uint hi = mulhi(a, b);
    uint m  = lo * NP;
    uint mp_hi = mulhi(m, P);
    uint t2 = hi + mp_hi + (lo != 0u ? 1u : 0u);
    return t2 >= P ? t2 - P : t2;
}
inline uint badd(uint a, uint b) {
    uint s = a + b;
    return s >= P ? s - P : s;
}
inline uint bsub(uint a, uint b) {
    return a >= b ? a - b : a + P - b;
}

kernel void bitrev(device const uint* src [[buffer(0)]],
                   device uint* dst [[buffer(1)]],
                   constant uint& lg [[buffer(2)]],
                   uint tid [[thread_position_in_grid]]) {
    uint j = reverse_bits(tid) >> (32u - lg);
    dst[j] = src[tid];
}

// one butterfly per thread; half = len/2; tid in [0, n/2)
kernel void stage(device uint* a [[buffer(0)]],
                  device const uint* tw [[buffer(1)]],
                  constant uint& half_log [[buffer(2)]],
                  constant uint& tw_off [[buffer(3)]],
                  uint tid [[thread_position_in_grid]]) {
    uint hl = 1u << half_log;
    uint j = tid & (hl - 1u);
    uint blk = tid >> half_log;
    uint pos = (blk << (half_log + 1u)) + j;
    uint w = tw[tw_off + j];
    uint u = a[pos];
    uint v = mont_mul(a[pos + hl], w);
    a[pos] = badd(u, v);
    a[pos + hl] = bsub(u, v);
}

kernel void scale(device uint* a [[buffer(0)]],
                  constant uint& c [[buffer(1)]],
                  uint tid [[thread_position_in_grid]]) {
    a[tid] = mont_mul(a[tid], c);
}
