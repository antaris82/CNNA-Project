#!/usr/bin/env python3
from __future__ import annotations
import csv
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
REFDIR = ROOT / 'derivation/registry/references'
BIB = ROOT / 'derivation/paper/bibliography/cnna_external_references.bib'


def rows(path: Path):
    with path.open(encoding='utf-8', newline='') as f:
        return list(csv.DictReader(f, delimiter='\t'))


def split_names(value: str) -> list[str]:
    return [x.strip() for x in value.split(';') if x.strip()]


def prose_names(value: str) -> str:
    names=split_names(value)
    if not names: return ''
    if len(names)==1: return names[0]
    if len(names)==2: return f'{names[0]} and {names[1]}'
    return ', '.join(names[:-1]) + f', and {names[-1]}'


def responsible_text(r: dict) -> str:
    if r.get('authors','').strip():
        return prose_names(r['authors'])
    return prose_names(r.get('editors','')) + ' (ed.)'


def compact_reference(r: dict) -> str:
    lead=responsible_text(r)
    title=f"*{r['title']}*"
    typ=r['reference_type']
    if typ=='journal_article':
        vol=r['volume']
        if r['issue']:
            vol += f"({r['issue']})"
        s=f"{lead}, {title}, {r['venue']} {vol} ({r['year']}), {r['pages']}."
    elif typ in {'book','edited_book'}:
        edition=f", {r['edition']} ed." if r.get('edition') else ''
        series=f", {r['series']}" if r.get('series') else ''
        s=f"{lead}, {title}{edition}{series}, {r['publisher']} ({r['year']})."
        if r.get('isbn'): s+=f" ISBN `{r['isbn']}`."
    else:
        s=f"{lead}, {title}, {r['publisher']} ({r['year']})."
    if r['doi']:
        s += f" DOI: `{r['doi']}`."
    else:
        s += f" DOI status: `{r['doi_status']}`."
    if r['arxiv_id']:
        s += f" arXiv: `{r['arxiv_id']}{r['arxiv_version']}`; arXiv DOI: `{r['arxiv_doi']}`."
    if typ not in {'journal_article','book','edited_book'}:
        s += f" Stable source: `{r['canonical_url']}`; accessed {r['accessed_date']}."
    return s


def bib_names(value: str) -> str:
    rendered=[]
    for name in split_names(value):
        if name.startswith('The ') or name.endswith(' Team') or name.endswith(' Community') or name=='M. Lothaire':
            rendered.append('{' + name + '}')
            continue
        parts=name.split()
        rendered.append(parts[-1] + ', ' + ' '.join(parts[:-1]) if len(parts)>=2 else name)
    return ' and '.join(rendered)


def bib_entry(r: dict) -> str:
    typ=r['reference_type']; key=r['bibtex_key']; fields=[]
    def add(name: str, value: str) -> None:
        if value: fields.append((name,value))
    if r.get('authors',''): add('author',bib_names(r['authors']))
    if r.get('editors',''): add('editor',bib_names(r['editors']))
    add('title',r['title'])
    if typ=='journal_article':
        entry_type='article'; add('journaltitle',r['venue']); add('year',r['year']); add('volume',r['volume']); add('number',r['issue']); add('pages',r['pages'])
    elif typ in {'book','edited_book'}:
        entry_type='book'; add('year',r['year']); add('publisher',r['publisher']); add('edition',r['edition']); add('series',r['series']); add('isbn',r['isbn']); add('pagetotal',r['pages'].split('--')[-1] if r['pages'].startswith('1--') else '')
    elif typ=='software_source':
        entry_type='software'; add('year',r['year']); add('organization',r['publisher']); add('version',r['source_version'] or ('Git commit '+r['source_commit'][:12]))
    else:
        entry_type='online'; add('year',r['year']); add('organization',r['publisher'])
    add('doi',r['doi'])
    if typ != 'software_source':
        add('url',r['doi_url'] or r['canonical_url'])
    if typ != 'software_source' and (not r['doi'] or typ in {'official_manual','software_release_documentation'}):
        add('urldate',r['accessed_date'])
    if r['arxiv_id']:
        add('eprint',r['arxiv_id']); add('eprinttype','arXiv')
    note=[]
    if r['source_version']: note.append(r['source_version'])
    if r['source_commit']: note.append('commit '+(r['source_commit'][:12] if typ=='software_source' else r['source_commit']))
    if r['arxiv_version']: note.append('arXiv '+r['arxiv_version'])
    if r['arxiv_doi']: note.append('arXiv DOI '+r['arxiv_doi'])
    if not r['doi'] and typ != 'software_source': note.append('no DOI assigned: '+r['doi_status'])
    add('note','; '.join(note).replace('_', r'\_'))
    lines=[f'@{entry_type}{{{key},']
    for idx,(name,value) in enumerate(fields):
        lines.append(f'  {name:<13} = {{{value}}}{"," if idx<len(fields)-1 else ""}')
    lines.append('}')
    return '\n'.join(lines)


def write_bibliography(refs: list[dict]) -> None:
    BIB.parent.mkdir(parents=True,exist_ok=True)
    BIB.write_text('\n\n'.join(bib_entry(r) for r in refs)+'\n',encoding='utf-8')


def rendered_content(u: dict, r: dict) -> str:
    if u['scope']=='MAIN_TEX': return f"\\cite[{u['citation_locator']}]{{{u['bibtex_key']}}}."
    if u['scope']=='SUPPLEMENT_MD':
        role='load-bearing theorem source' if u['load_bearing']=='true' else u['claim_role'].lower().replace('_',' ')
        return f"**{r['reference_id']} — {role}.** {compact_reference(r)} Exact location: {u['citation_locator']}. Context: {u['context_short']} Formal status: `{u['formalization_status']}`"
    if u['scope']=='REGISTRY_ONLY': return f"{compact_reference(r)} Context: {u['context_short']} Formal status: `{u['formalization_status']}`"
    raise ValueError(f"unsupported scope {u['scope']}")


def markers(scope: str, usage_id: str):
    return (f'% CNNA-EXTREF-BEGIN {usage_id}',f'% CNNA-EXTREF-END {usage_id}') if scope=='MAIN_TEX' else (f'<!-- CNNA-EXTREF-BEGIN {usage_id} -->',f'<!-- CNNA-EXTREF-END {usage_id} -->')


def replace_block(text: str, begin: str, end: str, content: str) -> str:
    if text.count(begin)!=1 or text.count(end)!=1: raise ValueError(f'expected exactly one marker pair: {begin}')
    left,rest=text.split(begin,1); _,right=rest.split(end,1)
    return left+begin+'\n'+content+'\n'+end+right


def write_human_register(refs: list[dict], usages: list[dict]) -> None:
    lines=['# External references and exact use contexts','','Generated from the TSV registries; the TSV files are authoritative.','']
    for r in refs:
        lines += [f"## {r['reference_id']} — `{r['bibtex_key']}`",'',compact_reference(r),'',f"Canonical URL: {r['canonical_url']}.",f"Alternate/direct source: {r['alternate_url'] or 'not recorded'}.",f"Verification: `{r['verification_status']}` against {r['metadata_verified_against']}.",f"Snapshot SHA-256: `{r['local_snapshot_sha256'] or 'not retained'}`.",'','Uses:']
        uses=[u for u in usages if u['reference_id']==r['reference_id']]
        lines += [f"- `{u['usage_id']}` — {u['id']} {u['paper_section']} / {u['scope']}: {u['context_short']} Locator: {u['citation_locator']}." for u in uses] or ['- none']
        lines.append('')
    (REFDIR/'EXTERNAL_REFERENCES.md').write_text('\n'.join(lines)+'\n',encoding='utf-8')


def main() -> None:
    refs=rows(REFDIR/'EXTERNAL_REFERENCES.tsv'); usages=rows(REFDIR/'EXTERNAL_REFERENCE_USAGE.tsv'); byref={r['reference_id']:r for r in refs}; changed=0
    for u in usages:
        target=ROOT/u['target_file']
        if not target.is_file():
            if u['scope']=='REGISTRY_ONLY': continue
            raise FileNotFoundError(target)
        begin,end=markers(u['scope'],u['usage_id']); text=target.read_text(encoding='utf-8'); new=replace_block(text,begin,end,rendered_content(u,byref[u['reference_id']]))
        if new!=text: target.write_text(new,encoding='utf-8'); changed+=1
    write_human_register(refs,usages); write_bibliography(refs)
    print(f'external_reference_renderer references={len(refs)} usages={len(usages)} changed_files={changed} PASS')

if __name__=='__main__': main()
