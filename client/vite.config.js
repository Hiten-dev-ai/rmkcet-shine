var __spreadArray = (this && this.__spreadArray) || function (to, from, pack) {
    if (pack || arguments.length === 2) for (var i = 0, l = from.length, ar; i < l; i++) {
        if (ar || !(i in from)) {
            if (!ar) ar = Array.prototype.slice.call(from, 0, i);
            ar[i] = from[i];
        }
    }
    return to.concat(ar || Array.prototype.slice.call(from));
};
import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';
import { visualizer } from 'rollup-plugin-visualizer';
var clientHost = process.env.HOST || 'localhost';
var serverOrigin = process.env.SERVER_ORIGIN || 'http://localhost:5001';
var allowedHosts = ['shine.athergrid.dev'];
var analyzeBundle = process.env.ANALYZE_BUNDLE === '1';
function sourceChunkName(id, marker, prefix) {
    var _a;
    var normalized = id.replace(/\\/g, '/');
    var markerIndex = normalized.indexOf(marker);
    if (markerIndex < 0)
        return undefined;
    var fileName = (_a = normalized.slice(markerIndex + marker.length).split('/')[0]) === null || _a === void 0 ? void 0 : _a.replace(/\.[tj]sx?$/, '');
    return fileName ? "".concat(prefix, "-").concat(fileName.replace(/[^a-z0-9_-]/gi, '-').toLowerCase()) : undefined;
}
export default defineConfig({
    plugins: __spreadArray([
        react()
    ], (analyzeBundle
        ? [visualizer({
                filename: 'dist/bundle-analysis.html',
                template: 'treemap',
                gzipSize: true,
                brotliSize: true,
            })]
        : []), true),
    build: {
        rollupOptions: {
            output: {
                manualChunks: function (id) {
                    if (id.includes('node_modules')) {
                        if (id.includes('react') || id.includes('@tanstack/react-query'))
                            return 'react';
                        if (id.includes('jspdf'))
                            return 'pdf';
                        return 'vendor';
                    }
                    var tabChunk = sourceChunkName(id, '/src/tabs/', 'tab');
                    if (tabChunk)
                        return tabChunk;
                    var featureChunk = sourceChunkName(id, '/src/features/', 'feature');
                    if (featureChunk)
                        return featureChunk;
                    if (id.includes('/src/runtime') || id.includes('/src/query'))
                        return 'runtime';
                    return undefined;
                },
            },
        },
    },
    server: {
        host: clientHost,
        port: 5000,
        strictPort: true,
        allowedHosts: allowedHosts,
        proxy: {
            '/api': {
                target: serverOrigin,
                changeOrigin: true,
            },
            '/auth': {
                target: serverOrigin,
                changeOrigin: true,
            },
        },
    },
    preview: {
        host: clientHost,
        port: 5000,
        strictPort: true,
        allowedHosts: allowedHosts,
        proxy: {
            '/api': {
                target: serverOrigin,
                changeOrigin: true,
            },
            '/auth': {
                target: serverOrigin,
                changeOrigin: true,
            },
        },
    },
});
