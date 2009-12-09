#!/bin/sh

act='launch Specware'

PATH=/bin:/usr/bin:/etc:/sbin:/usr/sbin:${PATH}

# Use the directory of this file as the value of SPECWARE4
SPECWARE4=`dirname $0`
export SPECWARE4

# Test whether SPECWARE4 has been set

if [ -z "$SPECWARE4" ]; then
    echo "Failed to $act, SPECWARE4 environment variable not set" 2>&1
    exit 1
fi

# Test whether SPECWARE4 is a directory

if [ ! -d "$SPECWARE4" ]; then
   echo "Failed to $act, $SPECWARE4 is not a directory" 2>&1
   exit 1
fi

SPECWARE_BIN=$SPECWARE4
cd $SPECWARE4

# Ensure SWPATH is set

if [ -z "$SWPATH" ]; then
  SWPATH="/"
  export SWPATH
fi

if [ -z "$IMAGE_EXTENSION" ]; then
   IMAGE_EXTENSION="sbclexe"
fi

#echo "\$IMAGE_EXTENSION=$IMAGE_EXTENSION"

LISP_HEAP_IMAGE="$SPECWARE_BIN"/Specware4."$IMAGE_EXTENSION"

"$LISP_HEAP_IMAGE" --eval "(progn (format t \"~%Welcome to Specware ~a~2%\" *Specware-Version*) (setq Emacs::*use-emacs-interface?* nil) (Specware::initializeSpecware-0) (SWShell::specware-shell t) (exit))"
