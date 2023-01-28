benchmarks = {
        "test_dram_dma":"22_03_16-045258",
        "3d_rendering":"22_03_17-205701",
        "bnn":"22_03_16-210531",
        "digit_recognition":"22_03_16-211232",
        "face_detection":"22_03_16-211934",
        "spam_filter":"22_03_16-212635",
        "optical_flow":"22_03_17-020330",
        "sssp":"22_03_17-021031",
        "sha256":"22_03_17-021732",
        "mobilenet":"22_03_17-022433"
}

class InterfaceMeta(object):
    """
    Metadata of recordable interfaces used in the evaluation
    """
    def __init__(self, name: str, record_width: int, validate_width: int):
        self.name = name
        self.record_width = record_width
        self.validate_width = validate_width
        self.total_width = record_width + validate_width

SWEEP_INTERFACES = [
    InterfaceMeta("sda", 100, 36),
    InterfaceMeta("ocl", 100, 36),
    InterfaceMeta("bar1", 100, 36),
    InterfaceMeta("pcim", 549, 775),
    InterfaceMeta("pcis", 775, 549),
]
SWEEP_INTERFACES_MAP = {
    intf.name : intf for intf in SWEEP_INTERFACES
}

sweep_configurations = [
        ("sda", "22_06_26-041253"),
        ("sda+ocl", "22_06_26-131929"),
        ("sda+ocl+bar1", "22_06_26-134359"),
        ("pcim", "22_06_28-035704"),
        ("sda+pcim", "22_06_28-050150"),
        ("sda+ocl+pcim", "22_06_28-052116"),
        ("sda+ocl+bar1+pcim", "22_06_26-141449"),
        ("pcim+pcis", "22_06_28-053205"),
        ("sda+pcim+pcis", "22_06_28-054119"),
        ("sda+ocl+pcim+pcis", "22_06_28-055119"),
        ("sda+ocl+bar1+pcim+pcis", "22_06_26-210743"),
]