# DAC-2025

Code for *Leveraging Critical Proof Obligations for Efficient IC3 Verification*

## Usage
---
### 1. Modified IC3ref 

To build:

```
IC3ref/minisat$ make
IC3ref$ make
```

To Run:

```
$ ./IC3 [-uc] [-pr] < <AIGER_file> 
```

- -uc: enable CPO-Driven UNSAT Core Generation
- -pr: enable CPO-Driven Proof Obligation Propagation

---

### 2. Modelchecker


To build:

```
modelchecker$ ./rebulid.sh
modelchecker$ make clean
modelchecker$ make -j
```

To Run:

```
$ ./modelchecker [-uc] [-pr] <AIGER_file> 
```
- -uc: enable CPO-Driven UNSAT Core Generation
- -pr: enable CPO-Driven Proof Obligation Propagation
