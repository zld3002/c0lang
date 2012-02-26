Sample vimrc file.  The stuff relevant to C0
is extracted into vimrc in this directory.                                                                     
======================================================================
                                            

"remove visual bell (ie annoying flashing)
set vb t_vb=

set expandtab

"remove special characters with a single (instead of multiple) backspace
set backspace=indent,eol,start

"searches as you enter search string
set incsearch

"scroll offset is 3 lines
set scrolloff=3

"set tab to 2 spaces
set tabstop=2

"set the autoindent to 2 spaces
set shiftwidth=2

"show the current row and column at the bottom of the screen
set ruler

"will wrap lines longer than 80 char to new visual line
set wrap

"enable syntax highlighting
syntax on

"enable filetype for command below
filetype on

"use c indentation style and syntax highlighting for c, c++, and c0 files
autocmd FileType c,cpp :set cindent
autocmd FileType c,cpp :setf c
autocmd FileType c,cpp :set expandtab
au BufEnter *.c0 setf c
au BufEnter *.c0 set cindent 
au BufEnter *.c0 set expandtab

"use python indentation style and syntax highlighting for python
autocmd FileType py set tabstop=4
autocmd FileType py set shiftwidth=4
autocmd FileType py set expandtab
autocmd FileType py setf python

" Sets how many lines of history VIM has to remember
set history=700

" Set to auto read when a file is changed from the outside
set autoread

" When vimrc is edited, reload it
autocmd! bufwritepost vimrc source ~/.vim_runtime/vimrc

"Ignore case when searching
set ignorecase 
set smartcase

"Highlight search things
set hlsearch 

"limit text lines to 80 characters. Will create new line when this is exceeded.
set textwidth=80 

"use this for black/dark terminal background
set background=dark

"use this for white/light terminal background
"set background=light

"show line numbers
"set number
