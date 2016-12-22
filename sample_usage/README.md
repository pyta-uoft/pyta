# Python TA Statistics

## Purpose

This module has been designed to calculate a series of statistics on a certain 
directory of Python files. This directory may be a single student's project
folder, or even the directory of an entire course worth of students' projects. 

## Calculated Statistics

`pyta_statistics` computes several statistics, both on the individual 
(per student) level, and the course (all students) level.

***Individual Statistics***

* Total number of messages of each type (code, style, both)
* Most frequent messages (code & style)
* Most frequent code errors
* Most frequent style errors

(The frequency statistics are presented in both raw and percentage form.)

***Aggregate Statistics***

* Five most frequent code errors (number of errors made)
* Average code errors per student
* Five most frequent style errors (number of errors made)
* Average style errors per student
* Five most frequent errors of either type (number of errors made)
* Average errors of either type per student
* "Five Number Summary" on the number of errors per student:
  * Most Errors: number of errors made by the student with the most errors 
  * Upper Quartile: 25% of students made at least this many errors
  * Median: the halfway point of errors per student
  * Lower Quartile: 25% of students made fewer than this many errors
  * Least Errors: number of errors made by the student with the least errors

## Instructions

In order to see the statistics for the files in a particular directory, 
call `pyta_statistics` on the absolute path to the directory, as so:
```python
>>> directory = "C:\\Users\\prof\\Documents\\course1\\projects"  # for example
>>> from sample_usage.pyta_stats import pyta_statistics          # while running python in the pyta directory
>>> pyta_statistics(directory)
```
The function will then return the compiled statistics, both individual and 
aggregate (if it is a course directory). 

## Modules

There are three Python files that contribute to the aggregation and calculation 
of statistics for Python TA:

* `sample_usage/pyta_stats.py`
  * This module contains the `pyta_statistics` function that users run on the
  directory that they want to analyse. It aggregates statistics that are collected 
  by `StatReporter` instances when `python_ta.check_all()` is run, then calls 
  the actual statistics calculators contained in the `stats_analysis` module, 
  and pretty-prints the results.

* `sample_usage/stats_analysis.py`
  * This module performs all of the actual statistics calculation on data collected 
  by `pyta_stats`. The main function, `summary`, takes in the data and calls 
  `_individual_calc` on every student/group's lists of errors, and also calls 
  helpers to calculate aggregate statistics on the entire directory/course's 
  worth of students. It returns all of this to `pyta_stats`, which prints 
  the results.

* `python_ta/reporters/stat_reporter.py` 
  * This Pylint-style `StatReporter` class is used by `python_ta.check_all()`, which 
  in turn calls `pylint`. An instance of `StatReporter` is created for every 
  file that is linted, and the errors reported are stored in class-level variables 
  that functions in other modules (i.e.: `pyta_statistics`) can then access.
  The class-level variables must be emptied for every new student/group's set 
  of files.
  (See Pylint documentation and the Python TA wiki for more on reporters.)
