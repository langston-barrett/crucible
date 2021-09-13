// f looks safe so long as its argument isn't MAX_INT, and g doesn't call it
// with MAX_INT.
int f(int x) __attribute__((noinline))  {
  return x + 1;
}

int g(int x) __attribute__((noinline))  {
  return f(0);
}
