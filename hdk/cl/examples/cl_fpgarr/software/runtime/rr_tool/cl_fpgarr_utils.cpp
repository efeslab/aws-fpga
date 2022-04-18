#include "cl_fpgarr_utils.hpp"
#include <algorithm>
bool findStringInArray(const char *s, size_t slen,
                                         const char *const * arr, size_t arrlen) {
  for (size_t i = 0; i < arrlen; ++i) {
    if (strncmp(s, arr[i], std::min(slen, std::strlen(arr[i]))) == 0)
      return true;
  }
  return false;
}
