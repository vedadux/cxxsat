cmake_minimum_required(VERSION 3.16)
project(cxxsat)
set(CMAKE_CXX_STANDARD 17)

include(ExternalProject)

set(BACKEND CADICAL)
# set(BACKEND CRYPTOMINISAT)

if("${BACKEND}" STREQUAL "CRYPTOMINISAT")
    message("Adding external Cryptominisat target")
    set(SOLVER_NAME cryptominisat)
    set(SOLVER_DIR ${PROJECT_SOURCE_DIR}/${SOLVER_NAME})
    set(SOLVER_BUILD_DIR ${SOLVER_DIR}/build)
    set(SOLVER_OPTIONS -DIPASIR=ON -DSTATICCOMPILE=OFF -DNOZLIB=ON)
    set(SOLVER_CONFIG_CMD cmake -B ${SOLVER_BUILD_DIR} ${SOLVER_OPTIONS})
    set(SOLVER_LIB_NAME lib${SOLVER_NAME})
    set(SOLVER_LIB_PATH ${SOLVER_BUILD_DIR}/lib/libipasircryptominisat5.so)
    set(SOLVER_LIB_LINKAGE SHARED)
elseif("${BACKEND}" STREQUAL "CADICAL")
    message("Adding external Cadical target")
    set(SOLVER_NAME cadical)
    set(SOLVER_DIR ${PROJECT_SOURCE_DIR}/${SOLVER_NAME})
    set(SOLVER_BUILD_DIR ${SOLVER_DIR}/build)
    set(SOLVER_OPTIONS )
    set(SOLVER_CONFIG_CMD ./configure)
    set(SOLVER_LIB_NAME lib${SOLVER_NAME})
    set(SOLVER_LIB_PATH ${SOLVER_BUILD_DIR}/libcadical.a)
    set(SOLVER_LIB_LINKAGE STATIC)
else()
    message(FATAL_ERROR "No valid backend provided, aborting.")
    die()
endif()

ExternalProject_Add(${SOLVER_NAME}
  SOURCE_DIR "${SOLVER_DIR}"
  DOWNLOAD_COMMAND  git submodule init && git submodule update
  CONFIGURE_COMMAND cd ${SOLVER_DIR} && ${SOLVER_CONFIG_CMD}
  BUILD_COMMAND     cd ${SOLVER_BUILD_DIR} && make -j4
  BUILD_BYPRODUCTS ${SOLVER_LIB_PATH}
  INSTALL_COMMAND   ""
  )
add_library(${SOLVER_LIB_NAME} ${SOLVER_LIB_LINKAGE} IMPORTED)
set_target_properties(${SOLVER_LIB_NAME} PROPERTIES
  IMPORTED_LOCATION "${SOLVER_LIB_PATH}"
  LINKER_LANGUAGE CXX)

add_library(cxxsat Solver.cpp VarManager.cpp vars.cpp)
target_link_libraries(cxxsat ${SOLVER_LIB_NAME})

enable_testing()
add_subdirectory(test)