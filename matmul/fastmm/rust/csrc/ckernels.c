/* the C library's D48 left-factor kernel and its pass driver (GCD, 64 row chunks), exported for
 * the Rust feasibility benchmark */
#include <dispatch/dispatch.h>
#include <stddef.h>

#include "kernels.h"

void c_dps48_l_f32(size_t m, size_t ld_in, size_t ld_out, const float *const *in, float *const *out, size_t r0,
                   size_t r1) {
    dps48_L_f(m, ld_in, ld_out, in, out, r0, r1);
}

void c_dps48_l_f64(size_t m, size_t ld_in, size_t ld_out, const double *const *in, double *const *out, size_t r0,
                   size_t r1) {
    dps48_L_d(m, ld_in, ld_out, in, out, r0, r1);
}

#define PASS(T, K)                                                                                      \
    size_t chunks = 64, step = (m + chunks - 1) / chunks;                                               \
    dispatch_apply(chunks, dispatch_get_global_queue(QOS_CLASS_USER_INTERACTIVE, 0), ^(size_t ch) {     \
        size_t r0 = ch * step, r1 = r0 + step < m ? r0 + step : m;                                      \
        if (r0 < r1) K(m, ld_in, ld_out, in, out, r0, r1);                                              \
    });

void c_pass_dps48_l_f32(size_t m, size_t ld_in, size_t ld_out, const float *const *in, float *const *out) {
    PASS(float, dps48_L_f)
}

void c_pass_dps48_l_f64(size_t m, size_t ld_in, size_t ld_out, const double *const *in, double *const *out) {
    PASS(double, dps48_L_d)
}
