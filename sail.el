(setq sail-font-lock-keywords
      (let* (
	     ;; define several category of keywords
             (x-keywords '("if" "else" "return" "while"))
	     (x-types '("float" "int" "string" "char" "bool" "null"))
	     (x-decls '("struct" "enum" "var" "sig" "mut" "method" "process"))
	     (x-coops '("await" "emit" "when" "watch" "spawn" "join"))
	     ;; generate regex string for each category of keywords
             (x-keywords-regexp (regexp-opt x-keywords 'words))
             (x-types-regexp (regexp-opt x-types 'words))
	     (x-decls-regexp (regexp-opt x-decls 'words))
	     (x-coops-regexp (regexp-opt x-coops 'words))
	     )
        `(
          (,x-types-regexp . 'font-lock-type-face)
          (,x-keywords-regexp . 'font-lock-keyword-face)
	  (,x-decls-regexp . 'font-lock-function-name-face)
	  (,x-coops-regexp . 'font-lock-builtin-face)
          )))

;;;###autoload
(define-derived-mode rea-mode c-mode "read mode"
  "Major mode for editing SAIL files"
  
  ;; code for syntax highlighting
  (setq font-lock-defaults '((sail-font-lock-keywords))))

;; add the mode to the `features' list
(provide 'sail-mode)

;;; sail-mode.el ends here
 
