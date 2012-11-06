

=========================
Emacs Usage in |Specware|
=========================

There are a number of emacs commands for |Specware| usage. We also
list some useful general-purpose commands. There is a |Specware| mode
for editing |Specware| files.

|Specware| Mode Commands
########################

These are the commands available when editing ``.sw`` files. Some of
them are available in the |Specware| menu in the menubar.

.. tabularcolumns:: |l|l|p{200pt}|

.. list-table::
   :widths: 65 140 210
   :header-rows: 1

   *  - Key
      - Name
      - Description
   *  - :kbd:`tab`
      - ``indent-line``
      - Indents line based on context.
   *  - ``linefeed``
      - ``newline-and-indent``
      - Same as return followed by tab.
   *  - :kbd:`M-tab`
      - ``back-to-outer-indent``
      - Indents line for outer expression.
   *  - :kbd:`M-C-q`
      - ``indent-sexp``
      - Indents parenthesized expression following point.
   *  - :kbd:`M-C-\``
      - ``indent-region``
      - Indents region.
   *  - :kbd:`M-*`
      - ``switch-to-lisp``
      - Switch to \*Specware Shell\* buffer.
   *  - :kbd:`M-.`
      - ``meta-point``
      - Prompts for op or type name (with default based on
        symbol at point), and goes to its definition. Searches only
        the units that have been loaded. First searches for
        definitions visible from the current unit.
   *  - :kbd:`M-,`
      - ``continue-meta-point``
      - If previous meta-point command returned more than one
        definition, go to the next definition. Can be repeated.
   *  - :kbd:`M-|`
      - ``electric-pipe``
      - Adds the skeleton of a new case to a case statement,
        properly indented.
   *  - :kbd:`C-c ;`
      - ``comment-region``
      - Comment out the region. With a negative argument
        uncomments the region.
   *  - :kbd:`C-c p`
      - ``process-current-file``
      - Does ``proc`` on current file. Also available in dired
        where it applies to the file on the current line. (This
        command will only work properly if the top-level directory for
        the file is in SWPATH).
   *  - :kbd:`C-c C-p`
      - ``process-unit``
      - Prompts for unitId to process. Defaults to unitId for
        the current file.
   *  - :kbd:`C-c g`
      - ``generate-lisp``
      - Does ``gen-lisp`` on current file. With an argument
        compiles and loads the generated lisp.
   *  - :kbd:`C-c C-l`
      - ``generate-lisp``
      - Does ``:swll`` on current file (generates lisp for
        local definitions of current file and compiles and loads
        them).
   *  - :kbd:`C-c h`
      - ``sw:convert-spec-to-haskell``
      - Generates Haskell code for current spec.
   *  - :kbd:`C-c H`
      - ``sw:convert-top-spec-to-haskell``
      - Generates Haskell code for current spec as the top
        level.
   *  - :kbd:`C-c !`
      - ``cd-current-directory``
      - Does a ``:cd`` in the \*Specware Shell\* buffer to the
        directory of the current file. Also available in dired.

|Specware| Interaction Commands
###############################

These are the commands available in the ``*Specware Shell*`` buffer.

.. tabularcolumns:: |l|l|p{250pt}|

.. list-table::
   :widths: 35 155 225
   :header-rows: 1

   *  - Key
      - Name
      - Description
   *  - :kbd:`M-.`
      - ``meta-point``
      - Prompts for op or type name (with default based on
        symbol at point), and goes to its definition. Searches only
        the units that have been loaded.
   *  - :kbd:`M-p`
      - ``previous-input``
      - Gets previous input.
   *  - :kbd:`M-r`
      - ``previous-matching-input``
      - Gets previous input matching regular expression
        (prompted for). Typically you can get a previous input by
        typing in a small substring. Repeating the command without
        changing the expression will find earlier matches.

Other Useful Emacs Commands
###########################

These are a few general Emacs commands which are useful when using
Specware. Commands with no key sequences are executed using :kbd:`M-x
name` . XEmacs can be customized using the ``Options`` menu. For
example, to make ``delete`` delete the selected region (as in most
Word Processing Programs), mouse ``Options`` , ``Editing`` ,
``Active Regions`` . To make the changes permanent, mouse
``Options`` , ``Save Options to Init File`` .

.. tabularcolumns:: |l|l|p{250pt}|

.. list-table::
   :widths: 60 125 230
   :header-rows: 1

   *  - Key
      - Name
      - Description
   *  - :kbd:`C-h`
      - ``help``
      - Help options. C-h m gives help about the current mode.
        Also see Help menu in menubar.
   *  - :kbd:`M-/`
      - ``dabbrev-expand``
      - Does symbol completion based on nearby words in buffer.
        Repeated key presses find additional completions.
   *  - :kbd:`C-sh- middle`
      - ``mode-motion-copy``
      - Copies the (highlighted) identifier or expression under
        the mouse to point.
   *  - |nbsp|
      - :kbd:`igrep`
      - Greps for string in files. Brings up buffer with
        matching lines. Mouse middle on a line to go to it. (In
        Windows requires installation of Cygwin.)
   *  - |nbsp|
      - ``igrep-find``
      - Like igrep but searches in all subdirectories.
   *  - |nbsp|
      - ``fgrep``
      - Like igrep except uses fgrep to search.
   *  - |nbsp|
      - ``fgrep-find``
      - Like igrep-find except uses fgrep to search. all
        subdirectories.
   *  - :kbd:`C-x C-f`
      - ``find-file``
      - Prompts for file to edit. tab does filename completion.
   *  - :kbd:`C-x d`
      - ``dired``
      - Prompts for directory to edit. Note that commands
        process-current-file and cd-current-directory described in the
        previous section are available in dired mode.
   *  - |nbsp|
      - ``viper-mode``
      - Vi emulation mode for people who like to edit using vi
        commands. Documentation is available under :kbd:`C-h i``.

X-Symbol Mode
#############

X-Symbol is an Emacs package that allows the appearance of non-ascii
symbols, such as mathematical operators and greek characters in file
buffers. The non-ascii symbols have ascii representations that are
stored in files, but converted to the non-ascii characters when the
files are read into an emacs buffer with X-Symbol mode turned on. For
example, the |Specware| symbol ``\_forall`` is displayed as |forall|
and ``\_or`` is displayed as |or|. All the ascii representations begin
with "\ ``\_``\ ". X-Symbol mode can be turned on and off by Toggling
``X-Symbol`` under ``Options`` in the ``Specware`` menu. When it is
on, there is an ``X-Symbol`` menu that provides several mechanisms for
entering X-Symbols. For example, the characters may be chosen directly
from the menu from different categories, such as |or| under the
``Operators`` sub-menu and |forall| under the ``Symbol`` sub-menu.
This sub-menu also shows keyboard commands for the symbol. E.g., the
keyboard shortcut for |or| is :kbd:`-= \/1`. Alternatively, you can
use the command :kbd:`c-,` after :kbd:`\/`. Repeated :kbd:`c-,` commands will
get you related X-Symbols. You can see all the available X-Symbols by
selecting ``GRID of Characters`` under ``Other Commands`` in the
``X-Symbol`` menu.
 

Hide/Show Commands
##################

There is experimental support for hiding bodies of specs, definitions
and other multi-line constructs. The main command for hiding is
``Shift-Middle-Click`` , i.e., holding down the shift key and middle-
clicking near the beginning of a multi-line construct. This will hide
all but the first line of the construct and display a ``...`` at the
end of the line to indicate that the body is hidden. Doing a shift-
middle-click on this line will expand the body. Thus shift-middle-
click acts as a hiding toggle.

There is a Hide/Show menu. The most useful commands it contains are
``Show All`` and ``Hide All``. ``Show All`` removes all hiding in
the file. ``Hide All`` hides the bodies of all top-level constructs.
I.e., if it is multi-unit file, the the bodies of the units will be
hidden, and if is a single-unit file then the bodies of multi-line
declarations such as definitions and axioms will be hidden.

