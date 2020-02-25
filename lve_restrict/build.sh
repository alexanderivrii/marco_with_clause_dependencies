#!/bin/sh
#CHANGE THE FOLLOWING LINE!
export MROOT=/gpfs/haifa/projects/n/namc/alexi/marco_with_clause_dependencies/lve_restrict
echo $MROOT
cd simp
/opt/rh/devtoolset-7/root/usr/bin/gmake clean
/opt/rh/devtoolset-7/root/usr/bin/gmake r
cp minisat_release ../lverestrict
#/opt/rh/devtoolset-7/root/usr/bin/gmake d
#cp minisat_debug ../lverestrict
