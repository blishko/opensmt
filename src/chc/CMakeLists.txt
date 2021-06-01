add_library(chc OBJECT "")

target_sources(chc
    PRIVATE ChcSystem.cc
    PRIVATE ChcInterpreter.cc
    PRIVATE ChcGraph.cc
    PRIVATE engine/AcceleratedBmc.cc
    PRIVATE engine/Bmc.cc
    PRIVATE engine/Lawi.cc
    PRIVATE engine/Spacer.cc
    PRIVATE engine/LoopAccelerator.cc
    PRIVATE engine/ReverseWrapper.cc
    PRIVATE TransitionSystem.cc
    PRIVATE Options.cc
    PRIVATE TermUtils.cc
    PRIVATE TransformationUtils.cc
    PRIVATE Validator.cc
    PRIVATE Normalizer.cc
    PRIVATE Witnesses.cc
    PRIVATE ModelBasedProjection.cc
    )
