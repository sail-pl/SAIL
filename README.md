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

An overview of the grammar is given below

id/uid respectively stand for identifier starting with lower/upper capital letter

-- Types include ground types, array types [type] and structure/enumeration types id<type,...,type>
-- a capital A stands for a generic type
-- a boxed type correspond to a heap allocated value

> type :=  
>         | bool  
>         | int  
>         | float  
>         | char  
>         | string  
>         | [type]  
>         | id [[<type,...,type>]]  
>         | box<type>  
>         | A  

-- A program is a sequence of definitions

> program := defn ... defn

-- Definitions may define structure/enumeration types, methods and processes
-- a process definition is actually a simple macro definition variables and signals declared as parameters
-- are simply substituted in the definition, the entry point of a program is a user-defined process named Main() 

> defn :=  
>         | struct id<A,...,A> {id:type,...,id:type}  
>         | enum id<A,...,A> {uid:(type,...,type),...,uid:(type,...,type)}  
>         | method id<A,...,A>(id:type,...,id:type) [[:type]] {stmt; .... stmt;}  
>         | process uid<A,...,A> (var id:type,...,id:type; signal id,...,id) {stmt; ... stmt;}  

# Statements

The execution of SAIL programs proceeds in successive steps called instants.
Parallel composition allows the concurrent execution of several processes.
At each instant signals may be present or absent. A signal is present either
because it is produces by the environment 
An instant terminates when all
processes are blocked, waiting for an absent signal. Signals are handled by the following
primitives :

- emit(s) : emits the signal s
- await(s) : awaits for the signal s
- watching (s) stmt : behaves as the statement stmt but is preempted at the 
  end of the instant if stmt if suspended and if s is present
  
SAIL supports pattern matching, a statement case(expr) {pat:stmt, ..., pat:stmt}
behaves as the first statement associated with a pattern matching the value denoted 
by the expression.
  

> stmt :=  
>         | var id = expr;                             (declaration of a variable)  
>         | signal id;                                 (declaration of a signal)  
>         | lhs = expr;                                (assignment)  
>         | {stmt; ... stmt;}                          (sequence)  
>         | {stmt || ... || stmt}                      (parallel composition)  
>         | if (expr) stmt [[else stmt]]               (conditional)  
>         | while (expr) stmt                          (loop)  
>         | case (expr) {pat:stmt, ..., pat:stmt}      (pattern matching)  
>         | id(expr, ..., expr);                       (call)  
>         | uid(expr, ..., expr);                      (macro)  
>         | return [[expr]];                           (return statement)  
>         | emit(id);                                  (emission of a signal)  
>         | await(id);                                 (blocking primitive, waiting for a signal)  
>         | watching(s) stmt                           (preemption)  

> expr :=  
>         | uid                                        (variable)  
>         | lit                                        (literal)   
>         | expr [expr]                                (read access in an array)  
>         | e.id                                       (read access in a structure)  
>         | (e)                                        (parenthesed expression) 
>         | - e                                        (usual unary operators)  
>         | e * e                                      (usual binary operator)  
>         | &e                                         (reference)  
>         | *e                                         (dereference)  
>         | [e;...;e]                                  (static array allocation)  
>         | {id : e; ...; id : e}                      (structure allocation)  
>         | uid(e,...,e)                               (enumeration allocation)  
>         | id(e,...,e)                                (method call)  

## left hand side

lhs :=  id | lhs.id | lhs[expr]  

## pattern
	
pat :=  id  | uid [[(pat, ..., pat)]]  

