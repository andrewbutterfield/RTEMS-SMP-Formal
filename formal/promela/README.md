# Promela/SPIN

`formal/promela`

This directory contains formal models written in Promela and tools that use SPIN to do test generation from those models.

## Contributors

* Andrew Butterfield
* Frédéric Tuong
* Robert Jennings
* Jerzy Jaśkuć
* Eoin Lynch
* James Gooding Hunt

## License

This project is licensed under the
[BSD-2-Clause](https://spdx.org/licenses/BSD-2-Clause.html) or
[CC-BY-SA-4.0](https://spdx.org/licenses/CC-BY-SA-4.0.html).

## Overview

The  Promela models and supporting material can be found in the `models` subdirectory.

The tools, written in Python3, are in the `src` directory.

## Testbuilder

### Model Naming

 * We use the same name for model, folder and root,
   based on Manual terminology, with "mgr" used to abbreviate "Manager". 
 * Names should be kept short
 * We only add "-model" to C sources placed into RTEMS test folders.
 
The names to be used are:

 * Barrier Manager: `barrier-mgr`
 * Chains: `chains`
 * Event Manager: `event-mgr`
 * Message Manager: `msg-mgr`
 * Semaphore Manager: `sem-mgr`

The role of `models.yml` is now simply to list all the currently available models.


