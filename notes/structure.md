Also check https://coq.inria.fr/tutorial/3-modules

This is from the chapter 2

We will need to import definitions from different files, with the following syntax:
```
From LF Require Export Basics.
```
To import the definitions, we need to have a `.vo` file (since we can only import compiled module files), in a directory associated with the prefix (LF in this case). To use these files, Coq needs a 
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
  
  
### `_CoqProject`
The second chapter tells us to add the folowing line 
```
-Q . LF
```

To our `_CoqProject` file. But what does it mean? 
Firsty, it's important to say that we use the Makefile to compile our .v files, and we do so with the help of both this Makefile and the `_CoqProject` file. They have separate jobs, as the makefile defines ~~how the compilation occurs~~ and the CoqProject maps the files for the coqc compiler. So, anytime we use the command `make`, coqc is invoked under the hood. Let's see.[

From `coqc` help page, we get some interesting info:
```
Coq options are:
  -I dir                 look for ML files in dir
  -include dir           (idem)
  -R dir coqdir          recursively map physical dir to logical coqdir
  -Q dir coqdir          map physical dir to logical coqdir
  -top coqdir            set the toplevel name to be coqdir instead of Top
```
So, when we call "make Basics.vo" for example, we are calling `coqc -Q . LF Basics.v`. The options defined in the CoqProject are the options we pass to the compiler. However, `make` also calculates dependencies between source files to compile them in the right order, so make should generally be preferred over explicit coqc.


**What are the logical coqdir and physical dir?**

Let's say we have this CoqProject file in the root of a directory that contains src/module, where the .v files lie. Let's also assume that we are creating a module (remember from the beginning of this text - coq works with modules) called LF.

Then, if we call `coqc -Q ./src/module Module`, we are telling Coq that our directory /src/module is a module called Module. It makes it possible to use imports from this directory, such as `From Module Require Export Something.`. We are importing `Somethin.vo` from the directory /src/module that corresponds, "logically", to Module.
