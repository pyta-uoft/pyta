# Python TA Statistics

## Purpose

This module has been designed to calculate a series of statistics on a certain 
directory of Python files. This directory may be a single student's project
folder, or even the directory of an entire course worth of students' projects. 

## Calculated Statistics

`pyta_statistics` computes several statistics, both on the individual 
(per student) level, and the course (all students) level.

***Individual Statistics***

* Most frequent code errors (raw and percentage)
* Most frequent style errors (raw and percentage)

***Aggregate Statistics***

* Most frequent code errors (raw and percentage)??? - num students or num errors?
* Most frequent style errors (raw and percentage)???
* Average code errors per student
* Average style errors per student
* "Five Number Summary" on total errors of students

## Instructions

In order to see the statistics for the files in a particular directory, 
call `pyta_statistics` on the absolute path to the directory, as so:
```python
>>> directory = "C:\\Users\\prof\\Documents\\course1\\projects"  # for example
>>> from sample_usage.pyta_stats import pyta_statistics
>>> pyta_statistics(directory)
```
The function will then return the compiled statistics, both individual and 
aggregate (if it is a course directory). 
