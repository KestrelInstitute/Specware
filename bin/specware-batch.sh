# This script reads commands from stdin and sends them to Specware, to
# be executed in batch mode.  It can be used with a 'here document'.

# Example of use:

# specware-batch.sh <<EOF
# proc ${SPECWARE4}/Library/CGen/Deep/C
# proc ${SPECWARE4}/Library/CGen/Deep/CPrettyPrinter_Tests
# ctext ${SPECWARE4}/Library/CGen/Deep/CPrettyPrinter_Tests
# e 1+1
# e run_test
# e 2+3
# quit
# EOF


# If SWPATH isn't set, things currently fail in a confusing way:
# To override this, set SWPATH before calling this script:
if [ -z $SWPATH ] ; then
    SWPATH="$SPECWARE4:/"
fi
export SWPATH

#FIXME: Perhaps die if this is not set by the caller?
# To override SBCL_SIZE, preset SBCL_SIZE before invoking this script.
SBCL_SIZE="${SBCL_SIZE:=2000}"
SPECWARE_EXECUTABLE="$SPECWARE4"/Applications/Specware/bin/unix/Specware4.sbclexe

"$SPECWARE_EXECUTABLE" --dynamic-space-size $SBCL_SIZE --eval "(progn (setq Emacs::*use-emacs-interface?* nil) (Specware::initializeSpecware-0) (SWShell::process-batch-commands) (sb-unix:unix-exit 0))"
