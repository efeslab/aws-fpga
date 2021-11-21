#include "cl_fpgarr_decoder.hpp"

void print_help() {
  puts("rr_tool: cfg_type cmd xxx.dump ...\n");
  puts("cfg_type ([r|v]) : r for record_bus_t, v for validate_bus_t\n");
  puts(
      "cmd ([d|c]) : d for dump (take one file), c for compare (take two "
      "files)\n");
  puts(
      "xxx.dump: trace dump files. each cmd has their own way to "
      "process multiple files\n");
}

template <typename BUSCFG>
int DecoderCmdExec(int argc, const char **argv) {
  int rc;
  if (argc < 1) {
    print_help();
    rc = -1;
  } else {
    switch (argv[0][0]) {
      case 'd': {
        if (argc < 2) {
          puts("Please give me a trace file\n");
          print_help();
          rc = -1;
        } else {
          printf("Parsing input file %s\n", argv[1]);
          Decoder<BUSCFG> d(argv[1]);
          d.gen_report(stdout);
          rc = 0;
        }
        break;
      }
      case 'c': {
        if (argc < 3) {
          puts("Please give me two trace files to compare");
          print_help();
          rc = -1;
        } else {
          Decoder<BUSCFG> d1(argv[1]);
          Decoder<BUSCFG> d2(argv[2]);
          // gen_compare_report return true when success
          // rc expects 0 to mean success
          rc = (d1.gen_compare_report(stdout, d2) != true);
        }
        break;
      }
      default:
        puts("Invalid cmd\n");
        print_help();
        rc = -1;
        break;
    }
  }
  return rc;
}
int main(int argc, const char **argv) {
  int rc;
  if (argc < 3) {
    print_help();
    rc = -1;
  } else
    switch (argv[1][0]) {
      case 'r':
        rc = DecoderCmdExec<record_bus_t>(argc - 2, argv + 2);
        break;
      case 'v':
        rc = DecoderCmdExec<validate_bus_t>(argc - 2, argv + 2);
        break;
      default:
        puts("Invalid cfg_type\n");
        print_help();
        rc = -1;
    }
  return rc;
}
