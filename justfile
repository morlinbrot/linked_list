default:
	just -l -u

alias mi := miri
miri *PARAMS:
	cargo watch -s "cargo +nightly miri test {{PARAMS}}"

alias t := test
test *PARAMS:
	cargo watch -x "test {{PARAMS}}"

alias c := clip
clip *PARAMS:
	cargo watch -x "clippy {{PARAMS}}"
