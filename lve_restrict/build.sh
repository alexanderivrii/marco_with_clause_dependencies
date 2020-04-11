#!/bin/sh

# Directory that contains this script
export MROOT=$(dirname $(readlink -f $0))

# Set to your system's equivalent of gmake
export MAKE=make
#export MAKE=/opt/rh/devtoolset-7/root/usr/bin/gmake

cd $MROOT/simp
$MAKE clean
$MAKE r

cp minisat_release ../lverestrict

#$MAKE d
#cp minisat_debug ../lverestrict
