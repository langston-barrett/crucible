#include <iostream>
#include <string>
int main(int argc, char const *argv[]) {
  std::string foo = "bar";

  if (rand() % 2) {
    std::cout << "foo=" << foo << '\n';
  } else {
    foo = "baz";
  }

  std::cout << "foo=" << foo << '\n';

  return 0;
}
