((nil
  ;; end in newline
  (require-final-newline . t)
  ;; spaces instead of tabs
  (indent-tabs-mode)
  ;; 80 columns of text
  (fill-column . 80)
  ;; no trailing whitespace
  (eval . (add-hook 'before-save-hook 'delete-trailing-whitespace nil t))))
