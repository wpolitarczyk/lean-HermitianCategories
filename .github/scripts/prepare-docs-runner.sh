#!/usr/bin/env bash
set -euo pipefail

echo 'Resources before swap setup'
free -h
swapon --show
df -h "$GITHUB_WORKSPACE" "$RUNNER_TEMP"

# Preserve existing swap. Leave at least 4 GiB free on the filesystem that
# holds the new swap file, and add up to 8 GiB for documentation generation.
swap_file="$RUNNER_TEMP/docs-runner.swap"
available_kib=$(df --output=avail -k "$RUNNER_TEMP" | tail -n 1 | tr -d ' ')
reserve_kib=$((4 * 1024 * 1024))
swap_gib=$(((available_kib - reserve_kib) / 1024 / 1024))
if ((swap_gib > 8)); then
  swap_gib=8
fi

if ((swap_gib < 1)); then
  echo '::warning::Less than 1 GiB is available for extra swap after reserving 4 GiB of disk space; continuing with existing swap.'
else
  echo "Adding ${swap_gib} GiB of swap at $swap_file"
  sudo install -m 600 /dev/null "$swap_file"
  sudo fallocate -l "${swap_gib}G" "$swap_file"
  sudo mkswap "$swap_file"
  sudo swapon "$swap_file"
fi

echo 'Resources after swap setup'
free -h
swapon --show
df -h "$GITHUB_WORKSPACE" "$RUNNER_TEMP"
