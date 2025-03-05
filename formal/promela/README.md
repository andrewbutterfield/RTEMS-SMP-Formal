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
 * Task Manager: `task-mgr`

The role of `models.yml` is now simply to list all the currently available models.

## Model Status

Here we report the current state of the various models,
in order of development. 
The notation [n/N] reports the number of API calls modelled (n) vs. 
the total number of API calls in the manager (N).

### Status of `chains` [2/23]

Was used as an initial trial on how to do test generation.
It only models the unprotected versions of `get` and `append`.
There is no plan to model any more of these, 
as this is really sequential data-manipulation.

### Status of `event-mgr` [2/2]

All API calls have been fully modelled.

### Status of `msg-mgr` [3/11]

Modelled:  `create` `send` `receive`

(! some confusion regarding `construct` and `create`?)

### Status of `barrier-mgr` [5/5]

Seems complete

### Status of `sem-mgr` [7/7]

While all API calls are covered, the full range of options are not.

### Status of `task-mgr` [n/21]

**New** Actively under development

### Status of `proto_sem` [n/a]

This does not models RTEMS APIs, but is used to explore various sematic issues.

**New** Actively under development



