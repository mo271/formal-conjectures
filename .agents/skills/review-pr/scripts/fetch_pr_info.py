#!/usr/bin/env python3
"""Fetch PR metadata, description, reviews, and comments from GitHub."""

import sys
import json
import urllib.request
import urllib.error

def fetch_json(url):
    req = urllib.request.Request(url, headers={'User-Agent': 'Jetski-PR-Reviewer'})
    try:
        with urllib.request.urlopen(req) as resp:
            return json.loads(resp.read().decode('utf-8'))
    except urllib.error.HTTPError as e:
        print(f"HTTP Error {e.code}: {e.reason}", file=sys.stderr)
        return None
    except Exception as e:
        print(f"Error fetching {url}: {e}", file=sys.stderr)
        return None

def main():
    if len(sys.argv) < 2:
        print("Usage: fetch_pr_info.py <PR_NUMBER> [REPO]")
        sys.exit(1)

    pr_num = sys.argv[1].lstrip('#')
    repo = sys.argv[2] if len(sys.argv) > 2 else "google-deepmind/formal-conjectures"
    base = f"https://api.github.com/repos/{repo}"

    pr = fetch_json(f"{base}/pulls/{pr_num}")
    if not pr:
        print(f"Could not fetch PR #{pr_num}")
        sys.exit(1)

    print("=" * 80)
    print(f"PR #{pr_num}: {pr.get('title')}")
    print(f"Author: @{pr.get('user', {}).get('login')} | State: {pr.get('state')} | Merged: {pr.get('merged')}")
    print(f"Head branch: {pr.get('head', {}).get('ref')} -> Base branch: {pr.get('base', {}).get('ref')}")
    print("=" * 80)
    print("\n## PR Description:\n")
    print(pr.get('body') or "(No description provided)")
    print("\n" + "-" * 80)

    # Reviews (top-level review submissions)
    reviews = fetch_json(f"{base}/pulls/{pr_num}/reviews") or []
    if reviews:
        print(f"\n## Reviews ({len(reviews)}):\n")
        for r in reviews:
            author = r.get('user', {}).get('login', 'unknown')
            state = r.get('state', 'UNKNOWN')
            submitted = r.get('submitted_at', '')
            body = (r.get('body') or '').strip()
            print(f"### Review by @{author} [{state}] ({submitted}):")
            if body:
                print(f"{body}\n")
            else:
                print("(No summary comment)\n")
    else:
        print("\n## No top-level reviews submitted yet.\n")

    # Inline review comments
    review_comments = fetch_json(f"{base}/pulls/{pr_num}/comments") or []
    if review_comments:
        print(f"\n## Inline Review Comments ({len(review_comments)}):\n")
        for rc in review_comments:
            author = rc.get('user', {}).get('login', 'unknown')
            path = rc.get('path', '')
            line = rc.get('line') or rc.get('original_line') or '?'
            body = rc.get('body', '').strip()
            print(f"### @{author} on `{path}:{line}`:\n{body}\n")
    else:
        print("\n## No inline review comments.\n")

    # Issue comments (general discussion outside review submissions)
    comments = fetch_json(f"{base}/issues/{pr_num}/comments") or []
    if comments:
        print(f"\n## General Conversation / Issue Comments ({len(comments)}):\n")
        for c in comments:
            author = c.get('user', {}).get('login', 'unknown')
            created = c.get('created_at', '')
            body = c.get('body', '').strip()
            print(f"### @{author} ({created}):\n{body}\n")
    else:
        print("\n## No general conversation comments.\n")

if __name__ == '__main__':
    main()
