(defconst sail-keywords-regex
  (regexp-opt '("if" "then" "else" "return" "while" "await" "emit" "watching" "run" "and" "signal" "var" "global" "when" "watching" "case") 'words))

(defconst sail-types-regex
  (regexp-opt '("float" "int" "string" "char" "bool") 'words))

(defconst sail-decls-regex
  (regexp-opt '("struct" "enum" "method" "module" "process" "where" "with" "as") 'words))

(defconst sail-constant-regex
  (regexp-opt '( "true" "false") 'words))


(defconst sail-font-lock-keywords
  (list
   (cons sail-keywords-regex 'font-lock-keyword-face)
   (cons sail-types-regex 'font-lock-type-face)
   (cons sail-decls-regex 'font-lock-function-name-face)
   (cons sail-constant-regex 'font-lock-constant-face)
   ))


(setq-default tab-width 4)

(setq starter (concat "^[ \t]*"(regexp-opt '("struct" "enum" "method" "module") t)))

(defun next-indent()
  (let ((counter 0))
    (save-excursion
      (beginning-of-line)
      (if (looking-at "^[ \t]*}") (incf counter))
      (while (< (point) (line-end-position))
        (when (looking-at (rx "{"))
          (incf counter))
        (when (looking-at (rx "}"))
          (decf counter))
        (forward-char 1)))
    counter
    )
  )

(defun sail-indent-line ()
  "Indent current line as SAIL code"
  (interactive)
  (beginning-of-line)
  (if (or (bobp) (looking-at starter))(indent-line-to 0)
    (let ((cur-indent 0))  
      (save-excursion
        (forward-line -1)
        (setq cur-indent (+ (current-indentation)
                            (* (next-indent) tab-width))))
      (beginning-of-line)
      (if (looking-at "^[ \t]*}")
          (setq cur-indent (- cur-indent tab-width)))
      (if (< cur-indent 0) (setq cur-indent 0))
      (indent-line-to cur-indent)
      )))



;;;###autoload
(add-to-list 'auto-mode-alist '("\\.sl\\'" . sail-mode))

(define-derived-mode sail-mode fundamental-mode "SAIL"
  "Major mode for editing SAIL files."
  (set (make-local-variable 'font-lock-defaults) '(sail-font-lock-keywords))
  (set (make-local-variable 'indent-line-function) 'sail-indent-line)
  )

(provide 'sail-mode)

;; (defvar sail-mode-syntax-table
;;   (let ((table (make-syntax-table)))
;; 	(modify-syntax-entry ?\{ "(} " table)
;; 	(modify-syntax-entry ?\} "){ " table)
;; 	(modify-syntax-entry ?\( "() " table)
;; 	(modify-syntax-entry ?\) ")( " table)
;; 	(modify-syntax-entry ?\[ "(] " table)
;;     (modify-syntax-entry ?\] ")[ " table)
;; 	(modify-syntax-entry ?< "." table)
;; 	(modify-syntax-entry ?> "." table)
;; 	(modify-syntax-entry ?* "." table)
;; 	(modify-syntax-entry ?/ "." table)
;;     (modify-syntax-entry ?+ "." table)
;;     (modify-syntax-entry ?- "." table)
;; 	(modify-syntax-entry ?% "." table)
	
;; 	table)
;;   "Syntax table for sail-mode")

;;; sail-mode.el ends here
 
