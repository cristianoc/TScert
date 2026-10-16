function staleRead(cell: { value: boolean | null }): boolean {
  if (cell.value !== null) {
    cell.value = null;
    return cell.value;
  } else {
    return false;
  }
}
