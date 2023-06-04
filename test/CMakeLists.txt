cmake_minimum_required(VERSION 3.25)
include(CTest)

add_executable(unit-solver unit-solver.cpp)
target_link_libraries(unit-solver libcxxsat)
target_include_directories(unit-solver PUBLIC ${PROJECT_SOURCE_DIR})

set(SOLVER_TESTS
  test_and)

foreach(TEST_NAME ${SOLVER_TESTS})
    add_test(NAME unit-solver:${TEST_NAME}
      COMMAND unit-solver ${TEST_NAME}
      WORKING_DIRECTORY .)
endforeach()