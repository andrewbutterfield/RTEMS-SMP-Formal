# Test Generation Tools

`formal/promela/src`

This directory contains tools that use SPIN to do test generation from Promela models.

## Contributors

* Andrew Butterfield
* Frédéric Tuong
* Robert Jennings
* James Gooding Hunt

Who else contributed to the python code?

## License

This project is licensed under the
[BSD-2-Clause](https://spdx.org/licenses/BSD-2-Clause.html) or
[CC-BY-SA-4.0](https://spdx.org/licenses/CC-BY-SA-4.0.html).


## Tool Setup

### Prerequisites

The Promela/SPIN tool is required. It can be obtained from [spinroot.com](https://spinroot.com). Follow the installation instructions there and ensure that the executable `spin` is on your `$PATH`.

### Tool Installation

From within `formal/promela/src` do:

```
make env
. env/bin/activate
make py
```

Alternatively, you can run `src.sh`.

You need to activate this virtual environment to use the toolset.

### Tool Configuration

The top-level program is `testbuilder.py`. 

It relies on a configuration file `testbuilder.yml` that defines various key names/paths related to your RTEMS installation. A template file `testbuilder-template.yml` is provided. This should be edited to reflect your setup, and then saved as `testbuilder.yml`.

Another configuration file `refine-config.yml` defines file names for files used during the test-generation process. A template file `refine-config-template.yml` is provided. This should be edited to reflect your setup, and then saved as `refine-config.yml`.

To simplify matters, it helps to create a short alias for the full pathname to `testbuilder.py`. This should be defined in `.bashrc` or similar.

```
alias tb=python3 path-to-formal/formal/promela/src/testbuilder.py
```

If all this is setup, then a quick test is simply to run the program without command line arguments, which will then issue a help statement:

```
:- tb
USAGE:
`allsteps <model> | allmodels | <list of models>` will run clean, spin, gentests, copy, compile and run for desired model(s)
`spin <model>` will run SPIN to find all scenarios
`gentests <model>` will produce C tests
`clean <model> | allmodels` will remove generated files.
`copy <model>`
   - copies the generated  C files to the relevant RTEMS test source directory
   - updates the relevant RTEMS configuration yaml file
`archive <model>`` will copy generated spn, trail, C, and test log files
   to the archive sub-directory of the current model directory.
`compile` rebuilds the RTEMS test executable
`run` runs the tests in the SIS simulator
`zero [model]` removes all generated C filenames from the RTEMS configuration yaml file. Yaml file based on global config if model not set, local config if model set.
  - it does NOT remove the test sources from the RTEMS test source directory
```

If there are obvious problems with `testbuilder.yml`, it will report an error.

Note: Both `testbuilder.yml` and `refine-config.yml` can be configured globally and on a per-model basis.
Model specific configuration can be created in the models' directory, eg `path-to-formal/formal/promela/models/chains/testbuilder.yml`.

Local configuration items will take precedence over their global counterparts.

### Automatic Test Generation

Automatic test generation is an extension of the test builder system that allows generation of tests based on models with multiple assertions and/or multiple LTL operations.

The top-level program is `automatic_testgen.py`.

It relies on `automatic-testgen.yml` which contains configuration items relating to SPIN arguments and other SPIN/Promela related items for Promela file and SPIN file creation. A template file `automatic-testgen-template.yml` is provided. This should be edited to reflect your setup, and then saved as `automatic-testgen.yml`.

It also relies on `testbuilder.yml` and `refine-config.yml` as above for information about RTEMS paths, and test file generation.

To simplify matters, it helps to create a short alias for the full pathname to `automatic_testgen.py`. This should be defined in `.bashrc` or similar.

```
alias au=python3 path-to-formal/formal/promela/src/automatic_testgen.py
```

If all this is setup, then a quick test is simply to run the program without command line arguments, which will then issue a help statement:

```
`genpmls <model>` will generate a promela file for each assertion or ltl
`spin <model>` will run SPIN to find all scenarios
`gentests <model>` will produce C tests
`clean <model>` will remove generated files.
`copy <model>`
   - copies the generated  C files to the relevant RTEMS test source directory
   - updates the relevant RTEMS configuration yaml file
`archive <model>` will copy generated spn, trail, C, and test log files
   to the archive sub-directory of the current model directory.
```

Note: `automatic-testgen.yml` can be configured globally and on a per-model basis.
Model specific configuration can be created in the models' directory, eg `path-to-formal/formal/promela/models/chains/automatic-testgen.yml`.

Local configuration items will take precedence over their global counterparts.

There are currently limitations to the automatic test generation framework.
It will not work with `tb allsteps allmodels` or `tb clean allmodels` as the systems have not yet been linked in that way.
The Promela parser will reject some valid Promela for Syntax errors.
This issue requires further investigation.

### Test Language Configuration

The default language for test files is c.

A file is required by the test-generation process to create files in any language.

This file exists for c at `path-to-formal/formal/promela/src/src/languages/c.yml`

If the desired language file does not exist you can create on in `path-to-formal/formal/promela/src/src/languages/`.
The file name must be lower-case to avoid errors.

The language for test generation can be set in the models refinement file using `LANGUAGE: your-language-here`.
An example can be found in `path-to-formal/formal/promela/models/barrier/barrier-mgr-model-rfn.yml`.

`refine-config.yml` must also be updated to reference language-specific pre-amble, post-amble and run files, as well as desired file extensions.
