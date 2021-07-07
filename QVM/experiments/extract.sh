#!/bin/bash

# Compile AltPQASM.
echo "Compiling AltPQASM..."
#coqc -R ../.. Top AltGateSet2.v
coqc -R ../.. Top AltPQASM.v

# Change into the extraction directory.
cd extraction

# Perform extraction.
echo "Extracting code..."
coqc -R ../../.. Top Extraction.v

# Remove unneeded files.
echo "Deleting unneeded files..."
rm -f *.glob *.mli *.vo*

# Remove empty/unused files.
rm -f ClassicalDedekindReals.ml ConstructiveCauchyReals.ml List.ml \
   QArith_base.ml Rdefinitions.ml Ring_theory.ml Rpow_def.ml Rtrigo1.ml \
   Specif.ml ZArith_dec.ml

# Move the remaining extracted files to the 'ml' subdirectory.
echo "Moving generated files to ml/..."
mv AltGateSet2.ml AltPQASM.ml Bin*.ml Bool.ml CLArith.ml Datatypes.ml Factorial.ml \
   QIMP.ml ModMult.ml Nat.ml PeanoNat.ml Prelim.ml RCIR.ml RZArith.ml PQASM.ml \
   FMapList.ml Order* OracleExample.ml \
   ml

# Build extracted code.
echo "Building extracted code..."
dune build run_qvm.exe