# Brunch League DC

Live standings for Brunch League DC: https://lavieboflip.github.io/brunch-league/

Scores live in `data/league.json` and are updated automatically from scorecards posted in the league GroupMe.

## Xtacle Invitational (flip cup)

- Player page (read-only, refreshes itself): https://lavieboflip.github.io/brunch-league/xtacle/
- Host desk (enter players and scores): https://lavieboflip.github.io/brunch-league/xtacle/admin.html

The host desk publishes to `xtacle/state.json` with a fine-grained GitHub token (Contents: read and write on this repo) that the host pastes into its Publish tab. The player page only reads that file.
