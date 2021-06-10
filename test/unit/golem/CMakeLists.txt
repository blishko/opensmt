add_executable(GolemTest)
target_include_directories(GolemTest PUBLIC "${PROJECT_SOURCE_DIR}/src/chc/engine")
target_sources(GolemTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_LAWI.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_MBP.cc"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_NNF.cc"
    )

target_link_libraries(GolemTest OpenSMT chc gtest gtest_main)
