ALL_HEADERS=$(wildcard *.hpp)
ALL_CPPS=$(wildcard *.cpp)
ALL_FILES=$(ALL_HEADERS) $(ALL_CPPS)
all: rr_tool.elf

rr_tool.elf: ${ALL_FILES}
	g++ -g --std=c++17 ${ALL_CPPS} -o $@
