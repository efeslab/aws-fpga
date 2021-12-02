ALL_HEADERS=$(wildcard *.hpp)
ALL_CPPS=$(wildcard *.cpp)
ALL_FILES=$(ALL_HEADERS) $(ALL_CPPS)
all: rr_tool.elf rr_tool.opt.elf

rr_tool.elf: ${ALL_FILES}
	g++ -g --std=c++17 ${ALL_CPPS} -o $@
rr_tool.opt.elf: ${ALL_FILES}
	g++ -g -O3 --std=c++17 ${ALL_CPPS} -o $@
