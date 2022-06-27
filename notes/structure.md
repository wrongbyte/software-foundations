We will need to import definitions from different files, with the following syntax:
```
From LF Require Export Basics.
```
To import the definitions, we need to have a `.vo` file, in a directory associated with the prefix (LF in this case). To use these files, Coq needs a 
"mapping" from `_CoqProject` (more on this below), that builds these files. By using CoqIDE, this compilation should happen automatically once you
submit the Require line.

### Compile from the command line

Coq uses a modules structure. We have a `coq_makefile` utility that is responsible for 
generating a Makefile for our project, and a `_CoqProject` that specifies the command line options to coqc and the 
target files.

The `coq_makefile_` is used to set up a build structure for the project based on makefiles, and we can invoke this command 
by running

```
coq_makefile -f _CoqProject -o CoqMakefile
```

This generates two files, a `CoqMakefile` and a `CoqMakefile.conf`. 
- `CoqMakefile`

  This is basically a makefile for the GNU make. We can then use `make` on our directory, and it will use the coq compiler, `coqc`.
  
- `CoqMakefile.conf`
  Contains make variables assignments that reflect the contents of the `_CoqProject` file as well as the path relevant to Coq.
  
  
