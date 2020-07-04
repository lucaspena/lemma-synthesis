all:
	time python3 dlist-list.py
	time python3 slist-list.py
	time python3 sdlist-dlist.py
	time python3 sdlist-dlist-and-slist.py
	time python3 listlen-list.py
	time python3 lseg-list.py
	time python3 listlen-list.py
	time python3 slseg-lseg.py
	time python3 list-find.py
	time python3 slist-find.py
	time python3 lseg-nil-list.py
	time python3 lseg-list-keys.py
	time python3 slseg-nil-list.py
	time python3 lseg-nil-length.py
	time python3 lseg-list-length.py

clean:
	rm -f *_KLemmas.txt
	rm -f out*.sy
	rm -f out*.smt2
