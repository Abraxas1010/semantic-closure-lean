// Minimal C source for WebAssembly export (no libc / no main).
// Derived from `add1.c` emitted by `closing_the_loop_bundle_demo`.

long long add1(long long x) {
  return (x + 1);
}

