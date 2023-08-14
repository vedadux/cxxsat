cmake_minimum_required(VERSION 3.16)
include(CTest)

add_executable(unit-solver unit-solver.cpp)
target_link_libraries(unit-solver cxxsat)
target_include_directories(unit-solver PUBLIC ${PROJECT_SOURCE_DIR})

set(SOLVER_TESTS
  test_and
  test_or
  test_xor
  test_mux
  test_and_multi
  test_or_multi
  test_at_most
  test_at_least
  test_add_clause
  test_operator
)

foreach(TEST_NAME ${SOLVER_TESTS})
    add_test(NAME unit-solver:${TEST_NAME}
      COMMAND unit-solver ${TEST_NAME}
      WORKING_DIRECTORY .)
endforeach()