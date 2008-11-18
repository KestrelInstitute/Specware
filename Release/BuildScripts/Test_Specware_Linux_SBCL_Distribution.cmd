#!/bin/sh

INVOKED_HERE=`dirname $0`
cd "$INVOKED_HERE"
HERE=`pwd`
cd "$HERE"

if [ "$1" == "" ]; then
  VERBOSE=nil
else
  VERBOSE=t
fi

echo "SPECWARE4    = $SPECWARE4"
echo "DISTRIBUTION = $DISTRIBUTION"

if [ -z "$SPECWARE4" ]; then
  echo "SPECWARE4 not defined"
  exit -1
fi

if [ -z "$DISTRIBUTION" ]; then
  echo "DISTRIBUTION not defined"
  exit -1
fi

if [ ! -d "$SPECWARE4" ]; then
  echo "Can't find Specware4 directory: $SPECWARE4"
  exit -1
fi

if [ ! -d "$DISTRIBUTION" ]; then
  echo "Can't find distribution directory: $DISTRIBUTION"
  exit -1
fi

/usr/local/bin/sbcl <<EOF
	(load "BuildSpecwareDistribution.lisp")
        (build-specware-test-release $VERBOSE)
	(quit)
EOF

