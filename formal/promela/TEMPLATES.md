# TEMPLATES

`formal/promela`

This directory contains formal models written in Promela and tools that use SPIN to do test generation from those models.

The  Promela models and supporting material can be found in the `models` subdirectory.

The tools, written in Python3, are in the `src` directory.

When the tools are in use, there are configuation files that point at cross-compilation tools and RTEMS source files.

## Plan

We need to separate `models` and `src`. 
Currently there are major linkages between the two. 
In particular, there are configuration files in `src` that provide links to models, tools and RTEMS sources.

Given interest in other OSes, it is now necessary to refactor this.

  * Step 1 - identify these linkages
  * Step 2 - plan how to disentangle them
  * Step 3 - disentsngle them

## linkages

Most of these are YAML files. 
The `src` distribution provides templates (`xxx-template.yml`) 
which are then instantiated for a given setup (renamed as `xxx.yml`).

Currently from `src`:
`automatic-testgen-template.yml`
, `testbuilder-template.yml`
, `refine-config-template.yml`

### Automatic Test Generation

### Refinement configuration

### Test Builder