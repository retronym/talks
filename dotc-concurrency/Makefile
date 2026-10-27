index.html: talk.md template.html build.py frames.json excerpts.gen.json
	python3 build.py

watch:
	@while true; do $(MAKE) -s index.html; sleep 1; done

.PHONY: watch

excerpts.gen.json: excerpts.json extract.py
	python3 extract.py

check:
	python3 extract.py --check

.PHONY: check
