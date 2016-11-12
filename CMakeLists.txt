CMAKE_MINIMUM_REQUIRED(VERSION 3.3)
PROJECT(CopyAndPasteDetector)

SET( CMAKE_BUILD_TYPE RELEASE )
SET( CMAKE_EXPORT_COMPILE_COMMANDS on )

SET( CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DCLANG_ENABLE_ARCMT -DCLANG_ENABLE_OBJC_REWRITER -DCLANG_ENABLE_STATIC_ANALYZER -std=c++14 -fvisibility-inlines-hidden -ffunction-sections -fdata-sections -fno-common -fno-strict-aliasing -Wl,--version-script,${CMAKE_SOURCE_DIR}/CopyAndPasteDetector.exports")

# put all libraries into a lib folder
SET(LIBRARY_OUTPUT_PATH ${PROJECT_BINARY_DIR}/lib)

# search for clang and libclang
find_package(Clang REQUIRED )

if ( Clang_FOUND ) 
  message ( "-- Clang Targets Found" )
endif()

find_package(LLVM REQUIRED)

if ( LLVM_FOUND ) 
  message ( "-- LLVM Targets Found" )
endif()

# for add_llvm_loadable_module
message( "-- Adding LLVM macros" ) 
list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
include(AddLLVM)

include_directories( plog/include )

# build the loadable module for the clang compiler
add_llvm_loadable_module( 
  CopyAndPasteDetector 
  CopyAndPasteDetector.cpp 
)

target_link_libraries( 
  CopyAndPasteDetector 
  clangASTMatchers 
  libclang 
  clangSema 
)

install ( TARGETS CopyAndPasteDetector 
  RUNTIME DESTINATION bin
  LIBRARY DESTINATION lib
)
