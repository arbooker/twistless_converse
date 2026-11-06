"""Hash computational inputs and retain recorded document provenance."""
from pathlib import Path
import hashlib
import json

_BASE = Path(__file__).resolve().parent
_INVENTORY = _BASE.parent / 'provenance' / 'SMALL_LEVEL_COMPANIONS_20261105.json'
_inventory = None
_inventory_sha256 = None
_recorded_documents = {}


def source_sha256(path):
    """Read file bytes, or use the inventory for a missing local document."""
    path = Path(path)
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except FileNotFoundError:
        if path.suffix.lower() not in {'.tex', '.bib'} or path.resolve().parent != _BASE:
            raise
    global _inventory, _inventory_sha256
    if _inventory is None:
        raw = _INVENTORY.read_bytes()
        _inventory = json.loads(raw)['files']
        _inventory_sha256 = hashlib.sha256(raw).hexdigest()
    digest = _inventory[path.name]['sha256']
    if len(digest) != 64 or any(c not in '0123456789abcdef' for c in digest):
        raise ValueError('Invalid recorded document hash: ' + path.name)
    _recorded_documents[path.name] = digest
    return digest


def recorded_document_provenance():
    """Identify document hashes obtained from the inventory, not a fresh read."""
    if not _recorded_documents:
        return {}
    return {
        'method': 'recorded_inventory',
        'inventory': 'provenance/' + _INVENTORY.name,
        'inventory_sha256': _inventory_sha256,
        'documents': dict(sorted(_recorded_documents.items())),
    }
