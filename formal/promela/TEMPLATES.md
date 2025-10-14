# TEMPLATES

`formal/promela`

This directory contains formal models written in Promela and tools that use SPIN to do test generation from those models.

The  Promela models and supporting material can be found in the `models` subdirectory.

The tools, written in Python3, are in the `src` directory.

When the tools are in use, there are configuation files that point at cross-compilation tools and RTEMS source files.

## Plan

We need to separate `models` and `src`. Currently there are major linkages between the two. In particular, there are configuration files in `src` that provide links to models, tools and RTEMS sources.

Given interest in other OSes, it is now necessary to refactor this.

  * Step 1 - identify these linkages - DONE
  * Step 2 - plan how to disentangle them
  * Step 3 - disentsngle them

## Linkages

Most of these are YAML files. The `src` distribution provides templates (`xxx-template.yml`) which are then instantiated for a given setup (renamed as `xxx.yml`).

Currently from `src`: `automatic-testgen-template.yml`, `refine-config-template.yml`, `testbuilder-template.yml`.


The first two templates are also currently the actual versions, 
while the third is were site-sprecific customisation is necessary.

### Automatic Test Generation

#### About 
This is all about negating `assert()` and `ltl` predicates, 
and parses and edits the Promela model itself.

#### Usage

Read from `automatic_testgen.py` which seems to be a standalone version of `testbuilder` that does selective `assert`/`ltl` negation.

#### Template 

```
disable_negation_at: [] 
spin_assert: -run -E -c0 -e 
spin_ltl: -run -E -c0 -e -ltl 
```

 * `disable_negation_at` : list of node names containing assertions not to negate.
 * `spin_assert` : trail generation for files with negated Assert "spin <spin_assert> <file_name>.pml"
 * `spin_ltl` : trail generation for files with negated LTL "spin <spin_ltl><ltl_name> <file_name>.pml"

#### Example

See Template above


### Refinement configuration

#### About

This defines the source code extension, and file-name suffixes for various files containing code snippets.

#### Usage

Read from `testbuilder.py`.

#### Template 

```
testfiletype: .c #tr-<model><test number><testfiletype>, tc-<model><testfiletype>
runfile: -run.h #<model><runfile>
preamble: -pre.h #<model><preamble>
postamble: -post.h #<model><postamble>
testcase_runfile: -run.h #tc-<model><runfile>
testcase_preamble: -pre.h #tc-<model><preamble>
testcase_postamble: -post.h #tc-<model><postamble>
refinefile: -rfn.yml #<model><refinefile>
```

#### Example

See Template above

#### Usage

### Test Builder

#### About

This was the original template and identifies python sources, and locations for model spurces, cross-compiler tools, and key parts of an operating system source setup.

#### Usage

Read from `testbuilder.py`.

#### Template

```
spin2test: <spin2test_directory>/spin2test.py
modelsfile: <formal_directory>/promela/models/models.yml
rtems: <path-to-main-rtems-directory>  # rtems.git, or ..../modules/rtems/
rsb: <rsb-build_directory>/rtems/6/bin/
simulator: <path-to>/sparc-rtems6-sis
testyamldir: <rtems>/spec/build/testsuites/validation/ # directory containing <modelname>.yml
testcode: <rtems>/testsuites/validation/
testexedir:  <rtems>/build/.../testsuites/validation/ # directory containing ts-<modelname>.exe
testsuite: model-0
simulatorargs: -leon3 -r s -m 2  # run command executes "<simulator> <simargs> <testexedir>/ts-<testsuite>.exe"
spinallscenarios: -DTEST_GEN -run -E -c0 -e # trail generation "spin <spinallscenarios> <model>.pml"
```

#### Example

Original RTEMS setup

```
spin2test: /Users/butrfeld/REPOS/RTEMS-SMP-Formal/formal/promela/src/spin2test.py
modelsfile: /Users/butrfeld/REPOS/RTEMS-SMP-Formal/formal/promela/models/models.yml
rtems: /Users/butrfeld/rtems/src/rtems/ 
rsb: /Users/butrfeld/rtems/6/bin/
simulator: /Users/butrfeld/rtems/6/bin/sparc-rtems6-sis
testyamldir: /Users/butrfeld/rtems/src/rtems/spec/build/testsuites/validation/ 
testcode: /Users/butrfeld/rtems/src/rtems/testsuites/validation/
testexedir:  /Users/butrfeld/rtems/src/rtems/build/sparc/leon3/testsuites/validation/
testsuite: model-0
simulatorargs: -leon3 -r s -m 4 
spinallscenarios: -DTEST_GEN -run -E -c0 -e 
```
