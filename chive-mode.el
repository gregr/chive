;; insert the following into .emacs; note the path may be different for you
;; (setq-default indent-tabs-mode nil) ; will set up a hook for this later...
;; (setq load-path
;;       (cons (expand-file-name "~/git/chive/") load-path))
;; (require 'chive-mode)
;; (add-to-list 'auto-mode-alist '("\\.chv\\'" . chive-mode))

;; (defvar chive-mode-hook nil)

;; (defvar chive-mode-map
;;   (let ((map (make-keymap)))
;;     (define-key map "\C-j" 'newline-and-indent)
;;     map)
;;   "Chive mode keymap")

(defvar chive-tab-width 2) ; how to use default-tab-width better?

(defun chive-wrap-angle (s) (concat "\\<" s "\\>"))

;; (defvar chive-keywords
;;   "\\<\\(__\\(?:abstract\\|ca\\(?:ll\\|se\\)\\|def_\\(?:syntax\\|var\\)\\|let\\(?:rec\\)?\\|macro\\)\\|operators?\\)\\>")

;; (defconst chive-font-lock-keywords
;;   (list
;;    '("" . font-lock-builtin-face)
;;    '("\\('\\w*'\\)" . font-lock-variable-name-face)
;;    '(chive-keywords . font-lock-keyword-face)
;; ;   '("" . font-lock-constant-face)
;;    '("\\(##.*\\)" . 'font-lock-comment-face)
;;    )
;;   "Chive mode expression highlighting")

(defvar chive-font-lock-keywords
  (list
;;   '("\\(\\sw+\\)" 1 font-lock-variable-name-face)
;   '("\\<\\(w+\\)\\>" 1 font-lock-variable-name-face)
;   `(,chive-builtins 1 font-lock-builtin-face)
;   `(,chive-keywords 1 font-lock-keyword-face)
   '("\\(`\\([a-zA-Z_]\\|\\(\\\\.\\)\\)\\([[:word:]]\\|\\(\\\\.\\)\\)*`\\)" 1 font-lock-variable-name-face)
 ;  '("\\(\\([a-zA-Z_]\\|\\(\\\\.\\)\\)\\([[:word:]]\\|\\(\\\\.\\)\\)*\\)" 1 font-lock-keyword-name-face)
   '("\\<\\([A-Z][A-Za-z0-9]+\\)" 1 font-lock-type-face)
   '("\\([`~!@$%^&*\\=+|;:,.<>/?-]*\\)" 1 font-lock-variable-name-face)
;;    '("\\([`~!@$%^&*\\=+|;:,.<>/?-]\\)" 1 font-lock-function-name-face)
;;   '("\\<\\([0-9]+\\)\\>" . font-lock-constant-face)
;   '("\\(##.*\\)" 0 'font-lock-comment-face)
   )
  "Chive mode expression highlighting")

(defun chive-nulldef (x def-x) (if (null x) def-x x))
(defun chive-cardef (xs def-x) (if (null xs) def-x (car xs)))

(defun chive-prev-cols ()
  ""
  (defun chive-prev-cols-inner (margin)
    (forward-line -1)
    (if (bobp) (list 0)
      (let ((cur (min (chive-nulldef margin (current-indentation))
		      (current-indentation))))
	(if (> cur 0)
	    (let ((next (chive-prev-cols-inner cur)))
	      (if (eq cur (car next)) next (cons cur next)))
	  (list 0)))))
  (save-excursion (chive-prev-cols-inner '())))

(defun chive-find-col (cur cols)
  ""
  (if (null cols) cols
    (if (eq cur (car cols)) (cdr cols)
      (chive-find-col cur (cdr cols)))))

(defun chive-next-indent ()
  ""
  (let* ((cur (current-indentation)) (cols (chive-prev-cols))
	 (most (+ (chive-cardef cols (- 0 chive-tab-width))
		  chive-tab-width))
	 (next (chive-cardef (chive-find-col cur (cons most cols)) most)))
    next))

(defun chive-indent-line ()
  "Chive mode indentation"
  (interactive)
  (if (bobp) (indent-line-to 0)
    (indent-line-to (chive-next-indent))))

(defvar chive-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?_ "w" st)
;    (modify-syntax-entry ?# ". 12b" st)
    (modify-syntax-entry ?\n "> b" st)
    st))

;; (defun chive-mode ()
;;   (interactive)
;;   (kill-all-local-variables)
;;   (use-local-map chive-mode-map)
;; ;  (set-syntax-table chive-mode-syntax-table)
;; ;  (set (make-local-variable 'font-lock-defaults) '(chive-font-lock-keywords))
;;   (set (make-local-variable 'indent-line-function) 'chive-indent-line)
;;   (setq major-mode 'chive-mode)
;;   (setq mode-name "Chive")
;;   (run-hooks 'chive-mode-hook))

(define-derived-mode chive-mode fundamental-mode "Chive"
   "Major mode for editing .chv files"
   :syntax-table chive-mode-syntax-table
;   (set (make-local-variable 'comment-start) "## ")
;   (set (make-local-variable 'comment-start-skip) "##+\\s-*") ; todo?
;;    (set (make-local-variable 'font-lock-keywords)
;; 	'(chive-font-lock-keywords))
   (set (make-local-variable 'font-lock-defaults)
	'(chive-font-lock-keywords))
   (set (make-local-variable 'indent-line-function) 'chive-indent-line)
;;    (set (make-local-variable 'imenu-generic-expression)
;; 	chive-imenu-generic-expression)
;;   (set (make-local-variable 'outline-regexp) chive-outline-regexp)
   )

(provide 'chive-mode)
