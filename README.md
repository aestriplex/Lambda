# Lambda [Work in progress]

A python library to automate the developing of symbolic tests that works on top of Z3 bindings.

## Requirements
* esprima
```
pip install esprima
```
* z3
```
pip install z3
```

## Demo

To tun a demo, you have to run 
```
python3 start.py
```

## Examples

You can see some examples of bounded model checking (both in STM-LIB2 and z3py) in doc/examples. The file `sample6.py` is also available on the official z3 repository

## Current developments

Currently I am developing:

* undefined variables and objects
* the bindings for the [JS standard library](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects)

## TODO
* Function call support
* References (and pointers) support
* Multithread support
