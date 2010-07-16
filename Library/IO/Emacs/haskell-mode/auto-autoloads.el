;;; DO NOT MODIFY THIS FILE
(if (featurep 'haskell-mode-autoloads) (error "Already loaded"))

;;;### (autoloads nil "_pkg" "haskell-mode/_pkg.el")

(package-provide 'haskell-mode :version 1.07 :author-version "1.45" :type 'regular)

;;;***

;;;### (autoloads (haskell-doc-show-type turn-off-haskell-doc-mode turn-on-haskell-doc-mode haskell-doc-mode) "haskell-doc" "haskell-mode/haskell-doc.el")

(defvar haskell-doc-mode nil "\
*If non-nil, show the type of the function near point or a related comment.

If the identifier near point is a Haskell keyword and the variable
`haskell-doc-show-reserved' is non-nil show a one line summary
of the syntax.

If the identifier near point is a Prelude or one of the standard library 
functions and `haskell-doc-show-prelude' is non-nil show its type.

If the identifier near point is local (i.e. defined in this module) check
the `imenu' list of functions for the type. This obviously requires that
your language mode uses `imenu' (`haskell-hugs-mode' 0.6 for example).

If the identifier near point is global (i.e. defined in an imported module) 
and the variable `haskell-doc-show-global-types' is non-nil show the type of its 
function.

If the identifier near point is a standard strategy or a function, type related
related to strategies and `haskell-doc-show-strategy' is non-nil show the type
of the function. Strategies are special to the parallel execution of Haskell.
If you're not interested in that just turn it off.

If the identifier near point is a user defined function that occurs as key
in the alist `haskell-doc-user-defined-ids' and the variable 
`haskell-doc-show-user-defined' is non-nil show the type of the function.

This variable is buffer-local.")

(autoload 'haskell-doc-mode "haskell-doc" "\
Enter `haskell-doc-mode' for showing fct types in the echo area.
See variable docstring." t nil)

(autoload 'turn-on-haskell-doc-mode "haskell-doc" "\
Unequivocally turn on `haskell-doc-mode' (see variable documentation)." t nil)

(autoload 'turn-off-haskell-doc-mode "haskell-doc" "\
Unequivocally turn off `haskell-doc-mode' (see variable documentation)." t nil)

(autoload 'haskell-doc-show-type "haskell-doc" "\
Show the type of the function near point.
For the function under point, show the type in the echo area.
This information is extracted from the `haskell-doc-prelude-types' alist
of prelude functions and their types, or from the local functions in the
current buffer." t nil)

;;;***

;;;### (autoloads (literate-haskell-mode haskell-mode) "haskell-mode" "haskell-mode/haskell-mode.el")

(autoload 'haskell-mode "haskell-mode" "\
Major mode for editing Haskell programs.  Last adapted for Haskell 1.4.
Blank lines separate paragraphs, comments start with `-- '.

\\<haskell-mode-map>\\[indent-for-comment] will place a comment at an appropriate place on the current line.
\\[comment-region] comments (or with prefix arg, uncomments) each line in the region.

Literate scripts are supported via `literate-haskell-mode'.  The
variable `haskell-literate' indicates the style of the script in the
current buffer.  See the documentation on this variable for more
details.

Modules can hook in via `haskell-mode-hook'.  The following modules
are supported with an `autoload' command:

   `haskell-font-lock', Graeme E Moss and Tommy Thorn
     Fontifies standard Haskell keywords, symbols, functions, etc.

   `haskell-decl-scan', Graeme E Moss
     Scans top-level declarations, and places them in a menu.

   `haskell-doc', Hans-Wolfgang Loidl
     Echoes types of functions or syntax of keywords when the cursor is idle.

   `haskell-indent', Guy Lapalme
     Intelligent semi-automatic indentation.

   `haskell-simple-indent', Graeme E Moss and Heribert Schuetz
     Simple indentation.

   `haskell-hugs', Guy Lapalme
     Interaction with Hugs interpreter.

Module X is activated using the command `turn-on-X'.  For example,
`haskell-font-lock' is activated using `turn-on-haskell-font-lock'.
For more information on a module, see the help for its `turn-on-X'
function.  Some modules can be deactivated using `turn-off-X'.  (Note
that `haskell-doc' is irregular in using `turn-(on/off)-haskell-doc-mode'.)

Use `haskell-version' to find out what version this is.

Invokes `haskell-mode-hook' if not nil." t nil)

(autoload 'literate-haskell-mode "haskell-mode" "\
As `haskell-mode' but for literate scripts." t nil)
(add-to-list 'auto-mode-alist '("\\.\\(?:[gh]s\\|hi\\)$" . haskell-mode))
(add-to-list 'auto-mode-alist '("\\.l[gh]s$" . literate-haskell-mode))
(add-hook 'haskell-mode-hook 'turn-on-haskell-font-lock)
(add-hook 'haskell-mode-hook 'turn-on-haskell-decl-scan)
(add-hook 'haskell-mode-hook 'turn-on-haskell-doc-mode)
(add-hook 'haskell-mode-hook 'turn-on-haskell-indent)

;;;***

(provide 'haskell-mode-autoloads)
