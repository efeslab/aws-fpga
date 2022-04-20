#include "cl_fpgarr_buscfg.hpp"
#include "cl_fpgarr_encoder.hpp"
#include "cl_fpgarr_decoder.hpp"
#include "cl_fpgarr_trace_mutation.hpp"
#include <unistd.h>
#include <stdlib.h>
#include <getopt.h>

void print_help() {
  puts("rr_tool: [options] cfg_type cmd xxx.dump ...\n");
  puts("options:\n"
      "\t -d for dump/verbose\n"
      "\t --hbver2 to enable the end-end definiton of happens-before");
  puts("cfg_type ([-r|-v]) : -r for record_bus_t, -v for validate_bus_t\n");
  puts(
      "cmd ([-a FILE|-c FILE1 -c FILE2|-m FILE1 -m FILE2 -o OUT_FILE]) : \n"
      "-a for analyse (take one file),\n"
      "-c for compare (take two files)\n"
      "-m for mutation, FILE1 is record_trace, FILE2 is the validate_trace. "
        "-o to specify output file\n");
}

template <typename BUSCFG>
int DecoderCmdExec(const argoptions_t &options) {
  int rc = -1;
  switch (options.op_type) {
    case argoptions_t::OP_ANLYS: {
      VIDITrace<BUSCFG> T;
      Decoder<BUSCFG> d(options.anlys_filepath);
      d.parse_trace(T);
      T.gen_report(stdout, options.isVerbose);
      rc = 0;
      break;
    }
    case argoptions_t::OP_COMP: {
      VIDITrace<BUSCFG> T1, T2;
      Decoder<BUSCFG> d1(options.comp_filepaths[0]);
      d1.parse_trace(T1);
      Decoder<BUSCFG> d2(options.comp_filepaths[1]);
      d2.parse_trace(T2);
      rc = (T1.gen_compare_report(stdout, T2, options.isVerbose,
                                  options.enableHBVer2) != true);
      break;
    }
    default:
      rc = -1;
  }
  return rc;
}

template <typename REC_BUSCFG, typename VERIF_BUSCFG>
int MutationCmdExec(const argoptions_t &options) {
  assert(options.op_type == argoptions_t::OP_MUTATE);
  VIDITrace<REC_BUSCFG> rec_trace;
  VIDITrace<VERIF_BUSCFG> verif_trace;
  Decoder<REC_BUSCFG> din_rec(options.input_filepath[0]);
  din_rec.parse_trace(rec_trace);
  Decoder<VERIF_BUSCFG> din_verif(options.input_filepath[1]);
  din_verif.parse_trace(verif_trace);
  VIDITracePCIMOrderMutation<REC_BUSCFG, VERIF_BUSCFG> mutator(rec_trace,
                                                               verif_trace);
  mutator.mutateRecordTrace();
  Encoder<REC_BUSCFG> e(options.output_filepath);
  e.export_trace(rec_trace);
  return 0;
}

#define GETOPT_STRING "rva:c:m:o:d"
enum optEnum {
  OPT_HBVER2 = 0x100, // random value as the base to avoid ascii
};
static struct option long_options[] = {
  {"hbver2", no_argument, 0, OPT_HBVER2},
  {0, 0, 0, 0}
};
void parse_args(int argc, char *const argv[], argoptions_t *options) {
  int opt;
  while ((opt = getopt_long(argc, argv, GETOPT_STRING, long_options, NULL)) !=
         -1) {
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
      case 'm':
        options->op_type = argoptions_t::OP_MUTATE;
        if (options->input_filepath[0] == nullptr)
          options->input_filepath[0] = optarg;
        else
          options->input_filepath[1] = optarg;
        break;
      case 'o':
        options->output_filepath = optarg;
      case OPT_HBVER2:
        options->enableHBVer2 = true;
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
  switch (options.op_type) {
    case argoptions_t::OP_ANLYS:
    case argoptions_t::OP_COMP:
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
      break;
    case argoptions_t::OP_MUTATE:
      rc = MutationCmdExec<record_bus_t, validate_bus_t>(options);
      break;
    default:
      fprintf(stderr, "Invalid op_code\n");
      rc = -1;
  }
  return rc;
}
