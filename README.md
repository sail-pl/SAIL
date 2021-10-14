# SAIL

SAIL aims at improving safety in general purpose interactive programming language. It is a simple imperative 
programming language with support for synchronous concurrent processes. By synchronous, we mean that processes
share a logical clock as in Esterel like-language. Processes communicate through shared memory and synchronize
by means of broadcasted signals. Causality issues are put aside by delaying reaction to absences as in Fairthread/C.
As Esterel and Fairthread/C, SAIL is control oriented. 

SAIL stands for SAfe Interactive Language

The long term objectives are :

- provide a safe, garbage collection free, memory handling with an ownership based system dedicated to cooperative processes
  this part is largely inspired by the rust type system, adapted to cooperative programming
- support for efficient execution by scheduling memory independent processes in parallel
- separation logic based program proof

The language propose the following features
- ground data types, structures and enumeration
- imperative methods
- cooperative processes which may
  - emit signal
  - execute on behalf of a signal
  - preempt on behalf of a signal
  - spawn new processes

