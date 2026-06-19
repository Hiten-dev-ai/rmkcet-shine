import { useEffect, useMemo, useRef, useState } from 'react';
import type { ReactNode } from 'react';

type Column<T> = {
  key: string;
  label: ReactNode;
  width: string;
  className?: string;
  render: (row: T) => ReactNode;
};

type VirtualizedRowsTableProps<T> = {
  columns: Array<Column<T>>;
  rows: T[];
  rowKey: (row: T) => string;
  rowHeight?: number;
  maxHeight?: number;
  emptyMessage: string;
};

const OVERSCAN_ROWS = 8;

export function VirtualizedRowsTable<T>({
  columns,
  rows,
  rowKey,
  rowHeight = 60,
  maxHeight = 640,
  emptyMessage,
}: VirtualizedRowsTableProps<T>) {
  const [scrollTop, setScrollTop] = useState(0);
  const pendingScrollTopRef = useRef(0);
  const scrollFrameRef = useRef<number | null>(null);
  const templateColumns = useMemo(() => columns.map((column) => column.width).join(' '), [columns]);
  useEffect(() => () => {
    if (scrollFrameRef.current !== null) {
      window.cancelAnimationFrame(scrollFrameRef.current);
    }
  }, []);
  const viewportCount = Math.max(1, Math.ceil(maxHeight / rowHeight));
  const startIndex = Math.max(0, Math.floor(scrollTop / rowHeight) - OVERSCAN_ROWS);
  const endIndex = Math.min(rows.length, startIndex + viewportCount + OVERSCAN_ROWS * 2);
  const visibleRows = rows.slice(startIndex, endIndex);
  const totalHeight = rows.length * rowHeight;
  const offsetY = startIndex * rowHeight;

  return (
    <div className="virtualized-table-shell">
      <div className="virtualized-table-header" style={{ gridTemplateColumns: templateColumns }}>
        {columns.map((column) => (
          <div key={column.key} className={`virtualized-table-cell virtualized-table-head ${column.className || ''}`.trim()}>
            {column.label}
          </div>
        ))}
      </div>
      <div
        className="virtualized-table-body"
        style={{ maxHeight }}
        onScroll={(event) => {
          pendingScrollTopRef.current = event.currentTarget.scrollTop;
          if (scrollFrameRef.current !== null) return;
          scrollFrameRef.current = window.requestAnimationFrame(() => {
            scrollFrameRef.current = null;
            setScrollTop(pendingScrollTopRef.current);
          });
        }}
      >
        {rows.length ? (
          <div style={{ height: totalHeight, position: 'relative' }}>
            <div style={{ transform: `translateY(${offsetY}px)` }}>
              {visibleRows.map((row) => (
                <div
                  key={rowKey(row)}
                  className="virtualized-table-row"
                  style={{ gridTemplateColumns: templateColumns, minHeight: rowHeight }}
                >
                  {columns.map((column) => (
                    <div
                      key={column.key}
                      className={`virtualized-table-cell ${column.className || ''}`.trim()}
                    >
                      {column.render(row)}
                    </div>
                  ))}
                </div>
              ))}
            </div>
          </div>
        ) : (
          <div className="virtualized-table-empty">{emptyMessage}</div>
        )}
      </div>
    </div>
  );
}
