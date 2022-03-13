#include "cl_fpgarr_decoder.hpp"
#include <unistd.h>
#include <stdlib.h>

void print_help() {
  puts("rr_tool: [options] cfg_type cmd xxx.dump ...\n");
  puts("options: -d for dump/verbose\n");
  puts("cfg_type ([-r|-v]) : -r for record_bus_t, -v for validate_bus_t\n");
  puts("cmd ([-a FILE|-c FILE1 -c FILE2]) : -a for analyse (take one file), "
      "-c for compare (take two files)\n");
}

template <typename BUSCFG>
int DecoderCmdExec(const argoptions_t &options) {
  int rc;
  switch (options.op_type) {
    case argoptions_t::OP_ANLYS: {
      Decoder<BUSCFG> d(options.anlys_filepath);
      d.gen_report(stdout, options.isVerbose);
      break;
    }
    case argoptions_t::OP_COMP: {
      Decoder<BUSCFG> d1(options.comp_filepaths[0]);
      Decoder<BUSCFG> d2(options.comp_filepaths[1]);
      rc = (d1.gen_compare_report(stdout, d2, options.isVerbose) != true);
      break;
    }
    default:
      rc = -1;
  }
  return rc;
}

#define GETOPT_STRING "rva:c:d"
void parse_args(int argc, char *const argv[], argoptions_t *options) {
  int opt;
  while ((opt = getopt(argc, argv, GETOPT_STRING)) != -1) {
    switch (opt) {
      case 'r':
        options->cfg_type = argoptions_t::CFG_RECORD;
        break;
      case 'v':
        options->cfg_type = argoptions_t::CFG_VERIF;
        break;
      case 'a':
        options->op_type = argoptions_t::OP_ANLYS;
        options->anlys_filepath = optarg;
        break;
      case 'c':
        options->op_type = argoptions_t::OP_COMP;
        if (options->comp_filepaths[0] == nullptr)
          options->comp_filepaths[0] = optarg;
        else
          options->comp_filepaths[1] = optarg;
        break;
      case 'd':
        options->isVerbose = true;
        break;
      default:
        print_help();
        exit(-1);
    }
  }
}

int main(int argc, char *argv[]) {
  int rc;
  argoptions_t options;
  parse_args(argc, argv, &options);
  switch (options.cfg_type) {
    case argoptions_t::CFG_RECORD:
      rc = DecoderCmdExec<record_bus_t>(options);
      break;
    case argoptions_t::CFG_VERIF:
      rc = DecoderCmdExec<validate_bus_t>(options);
      break;
    default:
      fprintf(stderr, "Invalid cfg type\n");
      rc = -1;
  }
  return rc;
}
