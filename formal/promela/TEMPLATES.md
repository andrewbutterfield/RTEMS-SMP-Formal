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
  * Step 3 - disentangle them
  * Step 4 - generalise them.
  * Step 5 - instantiate another OS

### Step 2 (Plan)

We initially imagine two repositories, one for testbuilder, the other for all of the Promela models, YAML refinement, and RTEMS C test code pieces. We then envisage a third repository for another OSes' models, refinement and C test code.

The testbuilder repository will provide templates,
but not contain the ones instantiated for a given model/OS installation.
Instead we change to the relevant model directory,
and have it look there for the relevent instantiations of the configuration data.

The plan is to ultimately remove the line:
```
source_dir = os.path.dirname(os.path.realpath(__file__))
```
from `testbuilder.py`.

Initially we will work in the current repository, until we are sure that everything that has to move from `src` to `models` has done so. This involves both the disentangling and generalising steps.

A design choice: do we keep all settings in one YAML file (`testbuilder`) or do we split out various aspects such as model-checker, OS-specifics, and test-framework?

**Note:** *`testbuilder` currently looks in `src` for "global" settings, and in `models` for "local" settings.*

#### Python Sources
```
automatic_testgen.py
gentest.py
metrics.py
spin2test.py
testbuilder.py
testgen_ml.py
testgen_yaml.py
src/__init__.py
src/library.py
src/refine_command.py
src/spin2test.py
src/syntax_ml.py
src/syntax_pml.py
src/syntax_yaml.py
src/testgen.py
src/modules/comment_filter/comment_filter/language.py
src/modules/comment_filter/comment_filter/rfc.py
src/modules/promela_yacc/promela/ast.py
src/modules/promela_yacc/promela/lex.py
src/modules/promela_yacc/promela/yacc.py
```

#### Python Explicit Import Structure

```
automatic_testgen <- testbuilder
gentest <- src.spin2test as s2t
metrics
spin2test <-  src.spin2test
testbuilder
testgen_ml <- src.testgen                                     (via Coconut)
testgen_yaml <- src.testgen                                   (via Coconut)
src/__init__.py
src/library.py                                                (via Coconut)
src/refine_command.py
src/spin2test.py <- src.refine_command as refine
src/syntax_ml.py                                              (via Coconut)
  <- src.modules.comment_filter.comment_filter (language,rfc)
src/syntax_pml.py <- src.library, src.syntax_pml              (via Coconut)
src/syntax_yaml.py <- src.library, src.syntax_pml             (via Coconut)
src/testgen.py                                                (via Coconut)
  <- src.library, src.refine_command, src.syntax_ml, src.syntax_pml
     src.syntax_yaml, src.modules.promela_yacc.promela (ast,lex,yacc)
```

#### Testbuilder Startup

We focus on which config files get read when...

```
 478 : config = get_config(source_dir)
 369 :    with open(f"{source_dir}/testbuilder.yml") as file:
 370 :    global_config = yaml.load(file, Loader=yaml.FullLoader)
 482+: if len(sys.argv) >= 3: config = get_config(source_dir, sys.argv[2])
 373 :    if model_name and model_name != "allmodels":
 376 :    local_config_path = Path(model_path / "testbuilder.yml")
 486+: if sys.argv[2] != "allmodels": refine_config 
        = get_refine_config(source_dir, sys.argv[2],
                           model_to_path[sys.argv[2]],
                           model_to_roots[sys.argv[2]])
 403:      with open(f"{source_dir}/refine-config.yml") as file:
 404 :     global_config = yaml.load(file, Loader=yaml.FullLoader)
 407+:     if Path(f"{model_dir}/refine-config.yml").exists():
           with open(f"{model_dir}/refine-config.yml") as file:
           local_config = yaml.load(file, Loader=yaml.FullLoader)
```

What is clear is that `global_config` needs to come from the `promela/model` directory,
rather than the `promela/src` one. The overall logic is unchanged.


### Step 3 (Disentangle)

  1. Move instantiated config YAML files to `models/` (DONE).
  2. Add the contents of `automatic-testgen(-template).yml` next to Spin-related stuff in `testbuilder(-template).yml`, and modify `automatic_testgen.py` to refer to `testbuilder.yml`. Note that it already looks up its stuff from `model_dir` and not `source_dir`.
  3. Remove any attempts to lookup `src` for "global" settings. Instead these live at the top-level of `models/`.


### Step 4 (Generalise)

 1. Rename the five keys formerly from `testbuilder.py` that are too specific. This will also affect the template file.
 2. Specific handling needed for `testyamldir` which is used in commands `zero` and `copy`. The code for those will need a flag that enables this aspect of those commands.


### Step 5 (Instantiate other OS)

 1. Split the RTEMS-SMP-Formal repo into separate Testbuilder and RTEMS-Model repositories.
 2. Copy the Model repo and switch it to work with another operating system.


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

#### Resolution

This template should live wherever Promela/Spin relevant material is found. Currently this is under the `formal/promela/models` directory.

We also need to consider if `automatic_testgen.py` should be integrated into `testbuilder.py`. Then this template would be merged with whatever happens to the Promela/Spin material currently in `testbuilder.yml`.

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

#### Resolution

This material should exist wherever the test code and model-checker refinements are defined. Currently this happens under the `formal/promela/models` directory.

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

#### Resolution

Hmmmm. Where to begin?

First, some of the keys are far too Promela/Spin specific: `spin2test`, `spinallscenarios`, and other keys are far too RTEMS specific: `rtems`, `rsb`, `testyamldir`. The latter is unlikely to have any counterpart in other operating systems,
and is used to create `testyaml` which points to a testsuite specification item. It is used in the `zero` and `copy` commands.

Currently this all resides under the `formal/promela/src` directory.
