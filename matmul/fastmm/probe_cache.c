/* probe_cache.c: the bandwidth of a plain pass d = a + b (two arrays read, one written, f64, NEON) by where its
 * arrays live: in a core's level-1 cache, in the cluster's level-2 cache, or in main memory.  w threads at
 * user-interactive quality of service (the performance cores), each on its own three arrays of the given size,
 * for a fixed time; the rate counts the three arrays' bytes, as probe_nt.c does.  The figures label the machine
 * diagram of the mixed-levels report.
 *   probe_cache [-s seconds per point, default 0.5]
 * Sizes: 3 x 16 KB and 3 x 32 KB per thread (level 1: 128 KB data cache per performance core), 3 x 256 KB and
 * 3 x 512 KB per thread (level 2: 16 MB per cluster of five), 3 x 192 MB per thread (main memory). */
#include <arm_neon.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static void *alloc_t(size_t bytes) {
    void *p = NULL;
    if (posix_memalign(&p, 16384, bytes)) exit(1);
    memset(p, 1, bytes);
    return p;
}
static atomic_int stop, ready;
static size_t bytes_per_array;
typedef struct { double secs, bytes; } worker_t;

__attribute__((noinline)) static void add_pass(double *restrict d, const double *restrict a, const double *restrict b, size_t cnt) {
    for (size_t i = 0; i < cnt; i += 4) {
        vst1q_f64(d + i, vaddq_f64(vld1q_f64(a + i), vld1q_f64(b + i)));
        vst1q_f64(d + i + 2, vaddq_f64(vld1q_f64(a + i + 2), vld1q_f64(b + i + 2)));
    }
}

static void *worker(void *p) {
    worker_t *w = p;
    pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);
    /* the three arrays apart by an odd number of pages, so that they do not share cache sets */
    size_t slot = bytes_per_array + 5 * 16384;
    double *base = alloc_t(3 * slot), *a = base, *b = (double *)((char *)base + slot), *d = (double *)((char *)base + 2 * slot);
    size_t cnt = bytes_per_array / 8, chunk = cnt < ((size_t)1 << 18) ? cnt : (size_t)1 << 18;
    add_pass(d, a, b, cnt);
    atomic_fetch_add(&ready, 1);
    double t0 = now();
    double moved = 0;
    while (!atomic_load(&stop))
        for (size_t c = 0; c < cnt && !atomic_load(&stop); c += chunk) add_pass(d + c, a + c, b + c, chunk), moved += 3.0 * 8 * (double)chunk;
    w->secs = now() - t0;
    w->bytes = moved;
    free(base);
    return NULL;
}

int main(int argc, char **argv) {
    double secs = 0.5;
    for (int i = 1; i + 1 < argc; i += 2)
        if (!strcmp(argv[i], "-s")) secs = atof(argv[i + 1]);
    static const size_t kb[] = {16, 32, 256, 512, 192 * 1024};
    static const char *where[] = {"level 1", "level 1", "level 2", "level 2", "main memory"};
    static const int threads[] = {1, 2, 5, 10};
    printf("# plain pass d = a + b (f64, NEON), three arrays per thread, %.1f s per point; GB/s over all threads\n", secs);
    for (size_t s = 0; s < sizeof kb / sizeof *kb; s++) {
        printf("3 x %6zu KB per thread (%-11s):", kb[s], where[s]);
        for (size_t t = 0; t < sizeof threads / sizeof *threads; t++) {
            int w = threads[t];
            pthread_t th[16];
            worker_t wk[16];
            bytes_per_array = kb[s] << 10;
            atomic_store(&stop, 0);
            atomic_store(&ready, 0);
            for (int i = 0; i < w; i++) pthread_create(&th[i], NULL, worker, &wk[i]);
            while (atomic_load(&ready) < w) { struct timespec ts = {0, 1000000}; nanosleep(&ts, NULL); }
            struct timespec ts = {(time_t)secs, (long)((secs - (double)(time_t)secs) * 1e9)};
            nanosleep(&ts, NULL);
            atomic_store(&stop, 1);
            double gb = 0;
            for (int i = 0; i < w; i++) pthread_join(th[i], NULL), gb += wk[i].bytes / wk[i].secs / 1e9;
            printf("  %2d threads %7.1f (%6.1f per thread)", w, gb, gb / w);
        }
        printf("\n");
    }
    return 0;
}
