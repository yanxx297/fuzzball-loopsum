export OCAMLMAKEFILE=../ocaml/OCamlMakefile
export VINE_OCAMLDIR=../ocaml
export STP_OCAMLDIR=../stp/ocaml
export LIBASMIR=../libasmir
include $(LIBASMIR)/makefile.inc
export INCDIRS += ../stp ../stp/ocaml $(VINE_OCAMLDIR)
export EXTLIBDIRS += ../stp ../stp/ocaml
export LIBS += stpvc vine

# Include sources from ../ocaml in the automatically generated dependencies.
# It seems like there should be a more elegant way to do this.
export OCAMLDEP = ocamldep -I $(VINE_OCAMLDIR) -I $(STP_OCAMLDIR)


# common sources
export SOURCES = temu_state.mli temu_state.ml

RESULT = trace
# DOC_FILES=$(SOURCES)


# ocamlfind packages required
export PACKS = str extlib unix
export YFLAGS = -v


export CLIBS = asmir vex opcodes bfd iberty stdc++ 
CFLAGS := 
LDFLAGS :=

ifdef DEBUG
CFLAGS += -g
endif

ifdef PROFILE
CFLAGS += -p
LDFLAGS += -p
endif

LDFLAGS += $(LIBASMIR_LDFLAGS)

export CFLAGS
export LDFLAGS
export CLIBFLAGS= $(LDFLAGS)
export LIBDIRS = $(LIBASMIR)/src # ../appreplay ../stp ../stp/ocaml

OCAMLLDFLAGS := -warn-error -a+30
OCAMLFLAGS := -warn-error Aelz
ifdef PROFILE
OCAMLFLAGS += -p
endif
export OCAMLFLAGS

# merge everything but descriptions.
OCAMLDOCFLAGS = -m avlsoper

all: dncl

nodebug: ncl

bytecode: dcl top

vine_lib_doc: all htdoc


# You may also tell "make" at the command-line what kind of target to
# produce (e.g. "make nc").  Here all the possibilities with shortcuts
# between parenthesis:
# 
#    * byte-code                     (bc)
#    * byte-code-nolink              (bcnl)   - no linking stage
#    * byte-code-library             (bcl)
#    * native-code                   (nc)
#    * native-code-nolink            (ncnl)   - no linking stage
#    * native-code-library           (ncl)
#    * debug-code                    (dc)
#    * debug-code-nolink             (dcnl)   - no linking stage
#    * debug-code-library            (dcl)
#    * profiling-byte-code           (pbc)
#    * profiling-byte-code-library   (pbcl)
#    * profiling-native-code         (pnc)
#    * profiling-native-code-library (pncl)
#    * byte-code-dll                 (bcd)
#    * native-code-dll               (ncd)
#    * pack-byte-code              (pabc)
#    * pack-native-code            (panc)
#    * toplevel interpreter          (top)
#    * subprjs



include $(OCAMLMAKEFILE)
