# Supporting Code for Formalising Graph Algorithms with Coinduction

This Agda library contains the code supporting the paper 
"Formalising Graph Algorithms with Coinduction".

It can be compiled with Agda version 2.6.4 and the agda cubical library
v0.6 (https://github.com/agda/cubical/releases/tag/v0.6).

The README.agda file is organised to mirror the structure of the paper.

The directory Unsafe/ contains all of the code that does not pass Agda's 
checkers for one reason or another: we use the code in here only to display 
examples, not to support any theorems.
The README.agda file is compiled with the --safe flag.

The code is rendered in highlighted and clickable html: the [README](https://oisdk.github.io/formalising-graph-algorithms-with-coinduction/README.html), or [Everything](https://oisdk.github.io/formalising-graph-algorithms-with-coinduction/Everything.html).
