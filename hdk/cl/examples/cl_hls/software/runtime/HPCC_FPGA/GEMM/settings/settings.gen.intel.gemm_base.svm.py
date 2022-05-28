
def generate_attributes(num_replications, num_global_memory_banks=32):
    """
    Generates the kernel attributes for the global memory. They specify in which 
    global memory the buffer is located. The buffers will be placed using a 
    round robin scheme using the available global memory banks and the number of
    replications that should be generated (e.g. if a global memory contains multiple banks)

    @param num_replications Number of kernel replications
    @param num_global_memory_banks Number of global memory banks that should be used for generation

    @return Array of maps. Maps contain four keys: "in" and "out" for the attributes assigned to input and output 
            buffers in globa memory.
    """
    array_names = ["a", "b", "c", "out"]
    return [ {array_name : "__attribute__((buffer_location(\"host\")))" for array_name in array_names} for _ in range(num_replications)]